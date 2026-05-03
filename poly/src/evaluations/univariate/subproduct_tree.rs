//! Subproduct tree for fast multipoint evaluation and interpolation of
//! univariate polynomials at arbitrary (non-radix-2) point sets.
//!
//! This is the classical algorithm from von zur Gathen & Gerhard,
//! *Modern Computer Algebra* (Ch. 10). Given `n` distinct evaluation points
//! `x_0, ..., x_{n-1} ∈ F`, a [`SubproductTree`] supports:
//!
//! - [`SubproductTree::evaluate`] — evaluating any polynomial `f` at all `n`
//!   points in `O(M(n) log n)` field operations.
//! - [`SubproductTree::interpolate`] — reconstructing the unique polynomial
//!   of degree `< n` that takes prescribed values `y_0, ..., y_{n-1}` at the
//!   evaluation points, in `O(M(n) log n)`.
//! - [`SubproductTree::evaluate_derivative_at_nodes`] — computing `M'(x_i)`
//!   for each `i`, where `M(x) = ∏(x - x_i)` is the vanishing polynomial.
//!
//! Unlike [`Radix2EvaluationDomain`](crate::Radix2EvaluationDomain), there is
//! no requirement that the points form a multiplicative subgroup, a coset,
//! or have size `2^k`. They must only be distinct.
//!
//! For small `n`, the [`multipoint_evaluate`] and [`interpolate`] free
//! functions transparently fall back to naive `O(n^2)` algorithms.

use crate::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_ff::{FftField, Zero};
use ark_std::{vec, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// A node of the subproduct tree. Stores the monic product `poly` over a
/// subset of the evaluation points, and (for non-leaf / non-trivial nodes)
/// the precomputed inverse `rev(poly)^{-1} mod x^{deg(poly)}`, which lets any
/// modular reduction against `poly` run in `O(M(deg(poly)))`.
#[derive(Clone, Debug)]
struct SubproductNode<F: FftField> {
    poly: DensePolynomial<F>,
    rev_inv: DensePolynomial<F>,
}

impl<F: FftField> SubproductNode<F> {
    fn leaf(x: F) -> Self {
        // poly = x - x_i, rev(poly) = 1 - x_i * x, rev_inv mod x^1 = 1.
        let poly = DensePolynomial::from_coefficients_vec(vec![-x, F::one()]);
        let rev_inv = DensePolynomial::from_coefficients_vec(vec![F::one()]);
        Self { poly, rev_inv }
    }

    fn combine(left: &Self, right: &Self) -> Self {
        // Short-circuit the "padding 1" case used for odd-sized levels.
        if right.poly.degree() == 0 {
            return left.clone();
        }
        if left.poly.degree() == 0 {
            return right.clone();
        }
        let poly = &left.poly * &right.poly;
        let deg = poly.degree();
        let rev_inv = poly.reverse().inverse_mod_xk(deg);
        Self { poly, rev_inv }
    }
}

/// A subproduct tree built over a set of evaluation points `x_0, ..., x_{n-1}`.
///
/// Construct with [`SubproductTree::new`], then use [`evaluate`][Self::evaluate]
/// or [`interpolate`][Self::interpolate] for fast multipoint operations.
#[derive(Clone, Debug)]
pub struct SubproductTree<F: FftField> {
    /// `levels[0]` is the list of leaves `(x - x_i)`; each subsequent level
    /// pairs adjacent nodes and multiplies, so `levels.last()[0]` is the
    /// full vanishing polynomial `M(x) = ∏(x - x_i)`.
    levels: Vec<Vec<SubproductNode<F>>>,
    /// Number of actual points `n` (the tree may be padded with trivial
    /// "1" nodes on the right when a level has odd length).
    num_points: usize,
}

impl<F: FftField> SubproductTree<F> {
    /// Builds the subproduct tree for the given evaluation points.
    ///
    /// Runs in `O(M(n) log n)` field operations. Points need not be distinct
    /// for the tree itself to be well-formed, but [`evaluate`][Self::evaluate]
    /// and [`interpolate`][Self::interpolate] require distinctness to produce
    /// meaningful results.
    pub fn new(xs: &[F]) -> Self {
        assert!(!xs.is_empty(), "SubproductTree::new: need at least one point");
        let num_points = xs.len();

        let leaves: Vec<SubproductNode<F>> = {
            #[cfg(feature = "parallel")]
            {
                xs.par_iter().map(|&x| SubproductNode::leaf(x)).collect()
            }
            #[cfg(not(feature = "parallel"))]
            {
                xs.iter().map(|&x| SubproductNode::leaf(x)).collect()
            }
        };

        let mut levels: Vec<Vec<SubproductNode<F>>> = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let mut padded_cow;
            let padded: &[SubproductNode<F>] = if prev.len() % 2 == 0 {
                prev.as_slice()
            } else {
                padded_cow = prev.clone();
                padded_cow.push(SubproductNode {
                    poly: DensePolynomial::from_coefficients_vec(vec![F::one()]),
                    rev_inv: DensePolynomial::from_coefficients_vec(vec![F::one()]),
                });
                padded_cow.as_slice()
            };

            let next: Vec<SubproductNode<F>> = {
                #[cfg(feature = "parallel")]
                {
                    padded
                        .par_chunks_exact(2)
                        .map(|pair| SubproductNode::combine(&pair[0], &pair[1]))
                        .collect()
                }
                #[cfg(not(feature = "parallel"))]
                {
                    padded
                        .chunks_exact(2)
                        .map(|pair| SubproductNode::combine(&pair[0], &pair[1]))
                        .collect()
                }
            };
            levels.push(next);
        }

        Self { levels, num_points }
    }

    /// The vanishing polynomial `M(x) = ∏_i (x - x_i)` over the evaluation set.
    pub fn vanishing_polynomial(&self) -> &DensePolynomial<F> {
        &self.levels.last().unwrap()[0].poly
    }

    /// Number of evaluation points the tree was built on.
    pub const fn num_points(&self) -> usize {
        self.num_points
    }

    /// Evaluates `f` at all evaluation points. Output has length `num_points()`
    /// and the `i`-th entry is `f(x_i)`.
    ///
    /// Runs in `O(M(n) log n)` field operations, independent of the degree
    /// of `f` (once `f` is reduced mod the root `M(x)` at the top of the walk).
    pub fn evaluate(&self, f: &DensePolynomial<F>) -> Vec<F> {
        // Top-down traversal. At each level, reduce each parent remainder by
        // the two child moduli using the precomputed rev inverses.
        let mut current = vec![f.clone()];
        for level in (0..self.levels.len() - 1).rev() {
            let children = &self.levels[level];
            let reduced: Vec<DensePolynomial<F>> = {
                #[cfg(feature = "parallel")]
                {
                    current
                        .par_iter()
                        .enumerate()
                        .flat_map_iter(|(idx, a)| {
                            let l = &children[2 * idx];
                            let pair = children.get(2 * idx + 1);
                            let rl = reduce(a, l);
                            let rr = if let Some(r) = pair {
                                reduce(a, r)
                            } else {
                                // Odd right-child: it was padded with "1" and
                                // the parent equals the left child, so we
                                // never actually spawned a right remainder.
                                return ark_std::iter::once(rl).chain(None);
                            };
                            ark_std::iter::once(rl).chain(Some(rr))
                        })
                        .collect()
                }
                #[cfg(not(feature = "parallel"))]
                {
                    let mut v = Vec::with_capacity(children.len());
                    for (idx, a) in current.iter().enumerate() {
                        let l = &children[2 * idx];
                        v.push(reduce(a, l));
                        if let Some(r) = children.get(2 * idx + 1) {
                            v.push(reduce(a, r));
                        }
                    }
                    v
                }
            };
            current = reduced;
        }

        debug_assert_eq!(current.len(), self.num_points);
        current
            .into_iter()
            .map(|r| r.coeffs.first().copied().unwrap_or_else(F::zero))
            .collect()
    }

    /// For each evaluation point `x_i`, returns `M'(x_i)` where `M` is the
    /// vanishing polynomial. Equivalent to `tree.evaluate(&M.derivative())`
    /// but exposed for convenience — this is the Lagrange weight denominator
    /// and comes up in essentially every barycentric formula.
    pub fn evaluate_derivative_at_nodes(&self) -> Vec<F> {
        let m_prime = self.vanishing_polynomial().derivative();
        self.evaluate(&m_prime)
    }

    /// Interpolates the unique polynomial of degree `< num_points()` that
    /// takes value `ys[i]` at each `x_i`. Requires `ys.len() == num_points()`
    /// and distinct evaluation points.
    ///
    /// Runs in `O(M(n) log n)` field operations.
    pub fn interpolate(&self, ys: &[F]) -> DensePolynomial<F> {
        assert_eq!(
            ys.len(),
            self.num_points,
            "interpolate: ys length {} must match num_points {}",
            ys.len(),
            self.num_points,
        );
        // c_i = y_i / M'(x_i). Batch-invert for one field inverse total.
        let mut inv_weights = self.evaluate_derivative_at_nodes();
        ark_ff::batch_inversion(&mut inv_weights);
        let mut cs: Vec<F> = ys
            .iter()
            .zip(inv_weights.iter())
            .map(|(y, w)| *y * w)
            .collect();

        // Bottom-up combine: F_parent = P_L * F_R + P_R * F_L, where F_leaf_i = c_i.
        // Pad `cs` with zero for any "1"-padded positions at the bottom level, so
        // the indexing matches the tree levels. Padding contributes zero polynomials
        // which get absorbed without changing the result.
        if cs.len() < self.levels[0].len() {
            cs.resize(self.levels[0].len(), F::zero());
        }
        let mut current: Vec<DensePolynomial<F>> = cs
            .into_iter()
            .map(|c| DensePolynomial::from_coefficients_vec(vec![c]))
            .collect();

        for level in 0..self.levels.len() - 1 {
            let nodes = &self.levels[level];
            let next: Vec<DensePolynomial<F>> = {
                #[cfg(feature = "parallel")]
                {
                    current
                        .par_chunks(2)
                        .enumerate()
                        .map(|(idx, pair)| combine_lagrange(pair, &nodes[2 * idx..]))
                        .collect()
                }
                #[cfg(not(feature = "parallel"))]
                {
                    let mut v = Vec::with_capacity((current.len() + 1) / 2);
                    for (idx, pair) in current.chunks(2).enumerate() {
                        v.push(combine_lagrange(pair, &nodes[2 * idx..]));
                    }
                    v
                }
            };
            current = next;
        }

        debug_assert_eq!(current.len(), 1);
        current.into_iter().next().unwrap()
    }
}

/// Reduces `a` modulo `node.poly` using the precomputed reverse-inverse.
/// Implements Algorithm 9.5 from von zur Gathen & Gerhard.
fn reduce<F: FftField>(
    a: &DensePolynomial<F>,
    node: &SubproductNode<F>,
) -> DensePolynomial<F> {
    let m = node.poly.degree();
    if a.degree() < m {
        return a.clone();
    }
    let n = a.degree();
    let k = n - m + 1;

    // rev_n(A), truncated to its low k coefficients (higher ones don't
    // contribute to the low-k product with rev_inv).
    let a_rev = a.reverse();
    let a_rev_low =
        DensePolynomial::from_coefficients_slice(&a_rev.coeffs[..a_rev.coeffs.len().min(k)]);

    // The precomputed `node.rev_inv` is accurate to precision `m`. If k ≤ m it
    // suffices; otherwise (this happens in unbalanced trees where the node is
    // used under a parent of degree much larger than 2 * m) recompute at
    // precision k. The recomputation is only needed for a small number of
    // imbalanced reductions — the balanced bulk still hits the cache.
    let rev_inv_owned;
    let rev_inv_ref: &DensePolynomial<F> = if k <= m {
        &node.rev_inv
    } else {
        rev_inv_owned = node.poly.reverse().inverse_mod_xk(k);
        &rev_inv_owned
    };
    let rev_inv_low = DensePolynomial::from_coefficients_slice(
        &rev_inv_ref.coeffs[..rev_inv_ref.coeffs.len().min(k)],
    );

    // q_rev = a_rev * rev_inv mod x^k
    let q_rev = a_rev_low.mul_low(&rev_inv_low, k);

    // q = rev_{k - 1}(q_rev). Reverse the padded coefficient vector directly:
    // going through `DensePolynomial::reverse` would strip high-index zeros
    // of q_rev, which correspond to low-order zeros of the true quotient
    // (e.g. `q = x^2`, whose coefficient vector is `[0, 0, 1]`).
    let mut padded = q_rev.coeffs;
    padded.resize(k, F::zero());
    padded.reverse();
    let q = DensePolynomial::from_coefficients_vec(padded);

    // r = (a - q * poly) truncated to low m coefficients.
    let qp_low = q.mul_low(&node.poly, m);
    let mut r = a.coeffs.clone();
    r.truncate(m);
    for (slot, qp) in r.iter_mut().zip(qp_low.coeffs.iter()).take(m) {
        *slot -= qp;
    }
    DensePolynomial::from_coefficients_vec(r)
}

/// Given pair = [F_L, F_R] and the node slice containing [P_L, P_R, ...],
/// returns F_parent = P_L * F_R + P_R * F_L.
fn combine_lagrange<F: FftField>(
    pair: &[DensePolynomial<F>],
    nodes: &[SubproductNode<F>],
) -> DensePolynomial<F> {
    match pair.len() {
        1 => pair[0].clone(),
        2 => {
            let f_l = &pair[0];
            let f_r = &pair[1];
            let p_l = &nodes[0].poly;
            let p_r = &nodes[1].poly;
            if p_r.degree() == 0 {
                f_l.clone()
            } else if p_l.degree() == 0 {
                f_r.clone()
            } else {
                &(p_l * f_r) + &(p_r * f_l)
            }
        },
        _ => unreachable!("combine_lagrange: pair has unexpected length"),
    }
}

/// Evaluates `f` at each of `xs`, returning `[f(x_0), ..., f(x_{n-1})]`.
///
/// For small `xs`, this falls back to direct Horner evaluation at each point;
/// above a threshold it builds a [`SubproductTree`] internally and uses the
/// `O(M(n) log n)` fast algorithm. If you have many polynomials to evaluate
/// at the same `xs`, build the tree yourself and call
/// [`SubproductTree::evaluate`] to amortize the build cost.
pub fn multipoint_evaluate<F: FftField>(f: &DensePolynomial<F>, xs: &[F]) -> Vec<F> {
    const NAIVE_THRESHOLD: usize = 32;
    if xs.len() <= NAIVE_THRESHOLD {
        return xs.iter().map(|x| f.evaluate(x)).collect();
    }
    SubproductTree::new(xs).evaluate(f)
}

/// Interpolates the unique polynomial of degree `< xs.len()` that takes the
/// prescribed value `ys[i]` at each `xs[i]`. Requires `xs` distinct and
/// `xs.len() == ys.len()`.
///
/// For small inputs, this falls back to naive Lagrange; above a threshold it
/// uses the `O(M(n) log n)` subproduct-tree algorithm.
pub fn interpolate<F: FftField>(xs: &[F], ys: &[F]) -> DensePolynomial<F> {
    assert_eq!(
        xs.len(),
        ys.len(),
        "interpolate: xs and ys must have equal length"
    );
    const NAIVE_THRESHOLD: usize = 32;
    if xs.len() <= NAIVE_THRESHOLD {
        return naive_lagrange(xs, ys);
    }
    SubproductTree::new(xs).interpolate(ys)
}

fn naive_lagrange<F: FftField>(xs: &[F], ys: &[F]) -> DensePolynomial<F> {
    let n = xs.len();
    if n == 0 {
        return DensePolynomial::zero();
    }
    let mut result = DensePolynomial::zero();
    for i in 0..n {
        let mut num = DensePolynomial::from_coefficients_vec(vec![F::one()]);
        let mut den = F::one();
        for j in 0..n {
            if i == j {
                continue;
            }
            // Multiply num by (x - xs[j])
            num = &num * &DensePolynomial::from_coefficients_vec(vec![-xs[j], F::one()]);
            den *= xs[i] - xs[j];
        }
        let inv_den = den.inverse().expect("interpolate: duplicate x-coordinate");
        let scale = ys[i] * inv_den;
        // num *= scale
        let scaled: Vec<F> = num.coeffs.iter().map(|c| *c * scale).collect();
        result = &result + &DensePolynomial::from_coefficients_vec(scaled);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;
    use ark_std::test_rng;
    use ark_test_curves::bls12_381::Fr;

    fn rand_distinct<R: ark_std::rand::Rng>(n: usize, rng: &mut R) -> Vec<Fr> {
        // For these tests n is small enough that random sampling collisions are negligible.
        (0..n).map(|_| Fr::rand(rng)).collect()
    }

    #[test]
    fn vanishing_polynomial_matches_naive_product() {
        let rng = &mut test_rng();
        for n in [1usize, 3, 8, 15, 32] {
            let xs = rand_distinct(n, rng);
            let tree = SubproductTree::new(&xs);
            let expected: DensePolynomial<Fr> = xs.iter().fold(
                DensePolynomial::from_coefficients_vec(vec![Fr::from(1u64)]),
                |acc, &x| &acc * &DensePolynomial::from_coefficients_vec(vec![-x, Fr::from(1u64)]),
            );
            assert_eq!(tree.vanishing_polynomial(), &expected);
        }
    }

    #[test]
    fn multipoint_evaluate_matches_horner() {
        let rng = &mut test_rng();
        for (deg, n) in [(0usize, 1), (5, 8), (20, 33), (100, 64), (40, 100)] {
            let xs = rand_distinct(n, rng);
            let f = DensePolynomial::<Fr>::rand(deg, rng);
            let fast = multipoint_evaluate(&f, &xs);
            let slow: Vec<Fr> = xs.iter().map(|x| f.evaluate(x)).collect();
            assert_eq!(fast, slow, "deg={}, n={}", deg, n);
        }
    }

    #[test]
    fn multipoint_evaluate_via_tree_amortization() {
        let rng = &mut test_rng();
        let xs = rand_distinct(65, rng);
        let tree = SubproductTree::new(&xs);
        for deg in [0usize, 10, 50, 200] {
            let f = DensePolynomial::<Fr>::rand(deg, rng);
            let fast = tree.evaluate(&f);
            let slow: Vec<Fr> = xs.iter().map(|x| f.evaluate(x)).collect();
            assert_eq!(fast, slow, "deg={}", deg);
        }
    }

    #[test]
    fn evaluate_derivative_matches_product_formula() {
        let rng = &mut test_rng();
        for n in [2usize, 5, 17, 64] {
            let xs = rand_distinct(n, rng);
            let tree = SubproductTree::new(&xs);
            let fast = tree.evaluate_derivative_at_nodes();
            let slow: Vec<Fr> = (0..n)
                .map(|i| {
                    // M'(x_i) = prod_{j != i} (x_i - x_j)
                    let mut acc = Fr::from(1u64);
                    for j in 0..n {
                        if j != i {
                            acc *= xs[i] - xs[j];
                        }
                    }
                    acc
                })
                .collect();
            assert_eq!(fast, slow, "n={}", n);
        }
    }

    #[test]
    fn interpolate_round_trips_through_multipoint_eval() {
        let rng = &mut test_rng();
        for n in [1usize, 5, 16, 33, 100] {
            let xs = rand_distinct(n, rng);
            // Sample a random polynomial of degree < n and interpolate its evaluations.
            let f = DensePolynomial::<Fr>::rand(n.saturating_sub(1).max(1), rng);
            let ys = multipoint_evaluate(&f, &xs);
            let recovered = interpolate(&xs, &ys);
            // Compare by values; different coefficient vectors could normalize the
            // same polynomial differently if degree < n-1 due to trailing-zero strip.
            let recovered_ys = multipoint_evaluate(&recovered, &xs);
            assert_eq!(recovered_ys, ys, "n={}", n);
        }
    }

    #[test]
    fn interpolate_hits_target_values() {
        let rng = &mut test_rng();
        let n = 50;
        let xs = rand_distinct(n, rng);
        let ys: Vec<Fr> = (0..n).map(|_| Fr::rand(rng)).collect();
        let p = interpolate(&xs, &ys);
        for i in 0..n {
            assert_eq!(p.evaluate(&xs[i]), ys[i]);
        }
    }
}
