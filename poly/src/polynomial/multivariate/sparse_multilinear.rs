//! multilinear polynomial represented in sparse evaluation form

use ark_ff::{Field, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::polynomial::multivariate::{swap_bits, DenseMultilinearPolynomial};
use crate::polynomial::MultilinearPolynomialEvaluationForm;
use crate::{MVPolynomial, Polynomial};
use ark_std::fmt::{Debug, Formatter};
use ark_std::ops::{Add, AddAssign, Neg, Sub, SubAssign};
use ark_std::vec::Vec;
use ark_std::{fmt, UniformRand};
use hashbrown::HashMap;
use rand::Rng;

/// Stores a multilinear polynomial in sparse evaluation form.
#[derive(Clone, PartialEq, Eq, Hash, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct SparseMultilinearPolynomial<F: Field> {
    /// tuples of index and value
    pub evaluations: Vec<(usize, F)>,
    /// number of variables
    pub num_vars: usize,
}

impl<F: Field> SparseMultilinearPolynomial<F> {
    pub fn from_evaluations<'a>(
        num_vars: usize,
        evaluations: impl IntoIterator<Item = &'a (usize, F)>,
    ) -> Self {
        let bit_mask = 1 << num_vars;
        // check
        let evaluations = cfg_into_iter!(evaluations);
        let evaluations: Vec<_> = evaluations
            .map(|(i, v): &(usize, F)| {
                assert!(*i < bit_mask, "index out of range");
                (*i, *v)
            })
            .collect();

        Self {
            evaluations,
            num_vars,
        }
    }

    /// Outputs a random `l`-variate sparse multilinear polynomial.
    ///
    /// Note that as number of nonzero entries approach `2 ^ num_vars`,
    /// sampling will be very slow due to large number of collisions.
    pub fn rand_with_config<R: Rng>(
        num_vars: usize,
        num_nonzero_entries: usize,
        rng: &mut R,
    ) -> Self {
        assert!(num_nonzero_entries <= (1 << num_vars));

        let mut map = HashMap::new();
        for _ in 0..num_nonzero_entries {
            let mut index = usize::rand(rng) & ((1 << num_vars) - 1);
            while let Some(_) = map.get(&index) {
                index = usize::rand(rng) & ((1 << num_vars) - 1);
            }
            map.entry(index).or_insert(F::rand(rng));
        }
        let mut buf = Vec::new();
        for (arg, v) in map.iter() {
            if *v != F::zero() {
                buf.push((*arg, *v));
            }
        }
        let evaluations = map_to_tuples(&map);
        Self {
            num_vars,
            evaluations,
        }
    }

    /// Convert the sparse multilinear polynomial to dense form.
    pub fn to_dense_multilinear_poly(&self) -> DenseMultilinearPolynomial<F> {
        let mut evaluations: Vec<_> = (0..(1 << self.num_vars)).map(|_| F::zero()).collect();
        for &(i, v) in self.evaluations.iter() {
            evaluations[i] = v;
        }
        DenseMultilinearPolynomial::from_evaluations_vec(self.num_vars, evaluations)
    }
}

impl<F: Field> Polynomial<F> for SparseMultilinearPolynomial<F> {
    /// Point is a vector of field element whose dimension is number of variables.
    type Point = Vec<F>;

    fn degree(&self) -> usize {
        self.num_vars
    }

    fn evaluate(&self, point: &Self::Point) -> F {
        assert_eq!(point.len(), self.num_vars, "invalid point");
        self.partial_evaluate(&point).lookup_evaluation(0)
    }
}

impl<F: Field> MVPolynomial<F> for SparseMultilinearPolynomial<F> {
    fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Outputs an `l`-variate multilinear polynomial.
    ///
    /// For sparse polynomial, the number of non-zero entries is the square root of 2^`num_vars`.
    fn rand<R: Rng>(d: usize, num_vars: usize, rng: &mut R) -> Self {
        assert_eq!(
            d, num_vars,
            "total degree of multilinear polynomial should equal to number of variables"
        );
        Self::rand_with_config(num_vars, 1 << (num_vars / 2), rng)
    }
}

impl<F: Field> MultilinearPolynomialEvaluationForm<F> for SparseMultilinearPolynomial<F> {
    type PartialPoint = Vec<F>;

    /// Returns the evaluation of the polynomial at a point represented by index.
    ///
    /// Index represents a vector in {0,1}^`num_vars` in little endian form. For example, `0b1011` represents `P(1,1,0,1)`
    ///
    /// For Sparse multilinear polynomial, Lookup_evaluation takes linear time to the size of polynomial.
    fn lookup_evaluation(&self, index: usize) -> F {
        cfg_iter!(self.evaluations)
            .filter(|(i, _)| *i == index)
            .map(|(_, v)| *v)
            .next()
            .unwrap_or(F::zero())
    }

    fn relabel(&self, mut a: usize, mut b: usize, k: usize) -> Self {
        if a > b {
            // swap
            let t = a;
            a = b;
            b = t;
        }
        // sanity check
        assert!(
            a + k < self.num_vars && b + k < self.num_vars,
            "invalid relabel argument"
        );
        if a == b || k == 0 {
            return self.clone();
        }
        assert!(a + k <= b, "overlapped swap window is not allowed");
        Self {
            num_vars: self.num_vars,
            evaluations: cfg_iter!(self.evaluations)
                .map(|&(i, v)| (swap_bits(i, a, b, k), v))
                .collect(),
        }
    }

    fn partial_evaluate(&self, partial_point: &Self::PartialPoint) -> Self {
        let dim = partial_point.len();
        assert!(dim <= self.num_vars, "invalid partial point dimension");

        let window = ark_std::log2(self.evaluations.len()) as usize;
        let mut point = partial_point.as_slice();
        let mut last = tuples_to_map(&self.evaluations);

        // batch evaluation
        while !point.is_empty() {
            let focus_length = if point.len() > window {
                window
            } else {
                point.len()
            };
            let focus = &point[..focus_length];
            point = &point[focus_length..];
            let pre = precompute_eq(focus);
            let dim = focus.len();
            let mut result = HashMap::new();
            for src_entry in last.iter() {
                let old_idx = *src_entry.0;
                let gz = pre[old_idx & ((1 << dim) - 1)];
                let new_idx = old_idx >> dim;
                let dst_entry = result.entry(new_idx).or_insert(F::zero());
                *dst_entry += gz * src_entry.1;
            }
            last = result;
        }
        let evaluations = map_to_tuples(&last);
        Self {
            num_vars: self.num_vars - dim,
            evaluations,
        }
    }
}

impl<F: Field> Add for SparseMultilinearPolynomial<F> {
    type Output = SparseMultilinearPolynomial<F>;

    fn add(self, other: SparseMultilinearPolynomial<F>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, F: Field> Add<&'a SparseMultilinearPolynomial<F>>
    for &'b SparseMultilinearPolynomial<F>
{
    type Output = SparseMultilinearPolynomial<F>;

    fn add(self, rhs: &'a SparseMultilinearPolynomial<F>) -> Self::Output {
        // handle zero case
        if self.is_zero() {
            return rhs.clone();
        }
        if rhs.is_zero() {
            return self.clone();
        }

        assert_eq!(
            rhs.num_vars, self.num_vars,
            "trying to add non-zero polynomial with different number of variables"
        );
        // simply merge the evaluations
        let mut evaluations = HashMap::new();
        for &(i, v) in self.evaluations.iter().chain(rhs.evaluations.iter()) {
            *(evaluations.entry(i).or_insert(F::zero())) += v;
        }
        let evaluations: Vec<_> = cfg_into_iter!(evaluations)
            .filter(|(_, v)| !v.is_zero())
            .collect();

        Self::Output {
            evaluations,
            num_vars: self.num_vars,
        }
    }
}

impl<F: Field> AddAssign for SparseMultilinearPolynomial<F> {
    fn add_assign(&mut self, other: Self) {
        *self = &*self + &other;
    }
}

impl<'a, 'b, F: Field> AddAssign<&'a SparseMultilinearPolynomial<F>>
    for SparseMultilinearPolynomial<F>
{
    fn add_assign(&mut self, other: &'a SparseMultilinearPolynomial<F>) {
        *self = &*self + other;
    }
}

impl<'a, 'b, F: Field> AddAssign<(F, &'a SparseMultilinearPolynomial<F>)>
    for SparseMultilinearPolynomial<F>
{
    fn add_assign(&mut self, (f, other): (F, &'a SparseMultilinearPolynomial<F>)) {
        if !self.is_zero() && !other.is_zero() {
            assert_eq!(
                other.num_vars, self.num_vars,
                "trying to add non-zero polynomial with different number of variables"
            );
        }
        let other = Self {
            num_vars: other.num_vars,
            evaluations: cfg_iter!(other.evaluations)
                .map(|(i, v)| (*i, f * v))
                .collect(),
        };
        *self += &other;
    }
}

impl<F: Field> Neg for SparseMultilinearPolynomial<F> {
    type Output = SparseMultilinearPolynomial<F>;

    fn neg(self) -> Self::Output {
        Self::Output {
            num_vars: self.num_vars,
            evaluations: cfg_iter!(self.evaluations)
                .map(|(i, v)| (*i, -*v))
                .collect(),
        }
    }
}

impl<F: Field> Sub for SparseMultilinearPolynomial<F> {
    type Output = SparseMultilinearPolynomial<F>;

    fn sub(self, other: SparseMultilinearPolynomial<F>) -> Self {
        &self - &other
    }
}

impl<'a, 'b, F: Field> Sub<&'a SparseMultilinearPolynomial<F>>
    for &'b SparseMultilinearPolynomial<F>
{
    type Output = SparseMultilinearPolynomial<F>;

    fn sub(self, rhs: &'a SparseMultilinearPolynomial<F>) -> Self::Output {
        self + &rhs.clone().neg()
    }
}

impl<F: Field> SubAssign for SparseMultilinearPolynomial<F> {
    fn sub_assign(&mut self, other: Self) {
        *self = &*self - &other;
    }
}

impl<'a, 'b, F: Field> SubAssign<&'a SparseMultilinearPolynomial<F>>
    for SparseMultilinearPolynomial<F>
{
    fn sub_assign(&mut self, other: &'a SparseMultilinearPolynomial<F>) {
        *self = &*self - other;
    }
}

impl<F: Field> Zero for SparseMultilinearPolynomial<F> {
    fn zero() -> Self {
        Self {
            num_vars: 0,
            evaluations: Vec::new(),
        }
    }

    fn is_zero(&self) -> bool {
        self.num_vars == 0 && self.evaluations.is_empty()
    }
}

impl<F: Field> Debug for SparseMultilinearPolynomial<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "SparseMultilinearPolynomial(num_vars = {}, evaluations = [",
            self.num_vars
        )?;
        for i in 0..ark_std::cmp::min(8, self.evaluations.len()) {
            write!(f, "{:?}", self.evaluations[i])?;
        }
        if self.evaluations.len() > 8 {
            write!(f, "...")?;
        }
        write!(f, "])")?;
        Ok(())
    }
}

/// utility: precompute f(x) = eq(g,x)
fn precompute_eq<F: Field>(g: &[F]) -> Vec<F> {
    let dim = g.len();
    let mut dp = Vec::with_capacity(1 << dim);
    dp.resize(1 << dim, F::zero());
    dp[0] = F::one() - g[0];
    dp[1] = g[0];
    for i in 1..dim {
        let dp_prev = (&dp[0..(1 << i)]).to_vec();
        for b in 0..(1 << i) {
            dp[b] = dp_prev[b] * (F::one() - g[i]);
            dp[b + (1 << i)] = dp_prev[b] * g[i];
        }
    }
    dp
}

/// Utility: Convert tuples to hashmap.
fn tuples_to_map<F: Field>(tuples: &[(usize, F)]) -> HashMap<usize, F> {
    let mut map = HashMap::with_capacity(tuples.len());
    for &(i, v) in tuples {
        assert!(map.insert(i, v).is_none(), "duplicate entries")
    }
    map
}

fn map_to_tuples<F: Field>(map: &HashMap<usize, F>) -> Vec<(usize, F)> {
    cfg_iter!(map)
        .map(|(i, v)| (*i, *v))
        .filter(|&(_, v)| !v.is_zero())
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::polynomial::multivariate::sparse_multilinear::SparseMultilinearPolynomial;
    use crate::polynomial::MultilinearPolynomialEvaluationForm;
    use crate::{MVPolynomial, Polynomial};
    use ark_ff::Zero;
    use ark_std::ops::Neg;
    use ark_std::vec::Vec;
    use ark_std::{test_rng, UniformRand};
    use ark_test_curves::bls12_381::Fr;

    /// Some sanity test to ensure random sparse polynomial make sense.
    #[test]
    fn random_poly() {
        const NV: usize = 16;

        let mut rng = test_rng();
        // two random poly should be different
        let poly1 = SparseMultilinearPolynomial::<Fr>::rand(NV, NV, &mut rng);
        let poly2 = SparseMultilinearPolynomial::<Fr>::rand(NV, NV, &mut rng);
        assert_ne!(poly1, poly2);
        // test sparsity
        assert!(
            ((1 << (NV / 2)) >> 1) <= poly1.evaluations.len()
                && poly1.evaluations.len() <= ((1 << (NV / 2)) << 1),
            "{},{},{}",
            ((1 << (NV / 2)) >> 1),
            poly1.evaluations.len(),
            ((1 << (NV / 2)) << 1)
        );
    }

    #[test]
    /// Test if sparse multilinear polynomial evaluates correctly.
    /// This function assumes dense multilinear polynomial functions correctly.
    fn evaluate() {
        const NV: usize = 12;
        let mut rng = test_rng();
        for _ in 0..20 {
            let sparse = SparseMultilinearPolynomial::<Fr>::rand(NV, NV, &mut rng);
            let dense = sparse.to_dense_multilinear_poly();
            let point: Vec<_> = (0..NV).map(|_| Fr::rand(&mut rng)).collect();
            assert_eq!(sparse.evaluate(&point), dense.evaluate(&point));
            let sparse_partial = sparse.partial_evaluate(&point[..3].to_vec());
            let dense_partial = dense.partial_evaluate(&point[..3].to_vec());
            let point2 = (0..(NV - 3)).map(|_| Fr::rand(&mut rng)).collect();
            assert_eq!(
                sparse_partial.evaluate(&point2),
                dense_partial.evaluate(&point2)
            );
        }
    }

    #[test]
    fn arithmetic() {
        const NV: usize = 18;
        let mut rng = test_rng();
        for _ in 0..20 {
            let point = (0..NV).map(|_| Fr::rand(&mut rng)).collect();
            let poly1 = SparseMultilinearPolynomial::rand(NV, NV, &mut rng);
            let poly2 = SparseMultilinearPolynomial::rand(NV, NV, &mut rng);
            let v1 = poly1.evaluate(&point);
            let v2 = poly2.evaluate(&point);
            // test add
            assert_eq!((&poly1 + &poly2).evaluate(&point), v1 + v2);
            // test sub
            assert_eq!((&poly1 - &poly2).evaluate(&point), v1 - v2);
            // test negate
            assert_eq!(poly1.clone().neg().evaluate(&point), -v1);
            // test add assign
            {
                let mut poly1 = poly1.clone();
                poly1 += &poly2;
                assert_eq!(poly1.evaluate(&point), v1 + v2)
            }
            // test sub assign
            {
                let mut poly1 = poly1.clone();
                poly1 -= &poly2;
                assert_eq!(poly1.evaluate(&point), v1 - v2)
            }
            // test add assign with scalar
            {
                let mut poly1 = poly1.clone();
                let scalar = Fr::rand(&mut rng);
                poly1 += (scalar, &poly2);
                assert_eq!(poly1.evaluate(&point), v1 + scalar * v2)
            }
            // test additive identity
            {
                assert_eq!(&poly1 + &SparseMultilinearPolynomial::zero(), poly1);
                assert_eq!(&SparseMultilinearPolynomial::zero() + &poly1, poly1);
                {
                    let mut poly1_cloned = poly1.clone();
                    poly1_cloned += &SparseMultilinearPolynomial::zero();
                    assert_eq!(&poly1_cloned, &poly1);
                    let mut zero = SparseMultilinearPolynomial::zero();
                    let scalar = Fr::rand(&mut rng);
                    zero += (scalar, &poly1);
                    assert_eq!(zero.evaluate(&point), scalar * v1);
                }
            }
        }
    }

    #[test]
    fn relabel() {
        let mut rng = test_rng();
        for _ in 0..20 {
            let mut poly = SparseMultilinearPolynomial::rand(10, 10, &mut rng);
            let mut point: Vec<_> = (0..10).map(|_| Fr::rand(&mut rng)).collect();

            let expected = poly.evaluate(&point);

            poly = poly.relabel(2, 2, 1); // should have no effect
            assert_eq!(expected, poly.evaluate(&point));

            poly = poly.relabel(3, 4, 1); // should switch 3 and 4
            point.swap(3, 4);
            assert_eq!(expected, poly.evaluate(&point));

            poly = poly.relabel(7, 5, 1);
            point.swap(7, 5);
            assert_eq!(expected, poly.evaluate(&point));

            poly = poly.relabel(2, 5, 3);
            point.swap(2, 5);
            point.swap(3, 6);
            point.swap(4, 7);
            assert_eq!(expected, poly.evaluate(&point));

            poly = poly.relabel(7, 0, 2);
            point.swap(0, 7);
            point.swap(1, 8);
            assert_eq!(expected, poly.evaluate(&point));
        }
    }
}
