//! A sparse polynomial represented in coefficient form.
use crate::{
    polynomial::Polynomial,
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
    DenseUVPolynomial, EvaluationDomain, Evaluations,
};
use ark_ff::{FftField, Field, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    cfg_iter_mut,
    cmp::Ordering,
    collections::BTreeMap,
    fmt,
    ops::{Add, AddAssign, Deref, DerefMut, Mul, Neg, SubAssign},
    vec,
    vec::*,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Stores a sparse polynomial in coefficient form.
#[derive(Clone, PartialEq, Eq, Hash, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct SparsePolynomial<F: Field> {
    /// The coefficient a_i of `x^i` is stored as (i, a_i) in `self.coeffs`.
    /// the entries in `self.coeffs` *must*  be sorted in increasing order of
    /// `i`.
    pub coeffs: Vec<(usize, F)>,
}

fn merge_coefficients<F: Field>(
    lhs: &[(usize, F)],
    rhs: &[(usize, F)],
    map_rhs: impl Fn(F) -> F,
) -> Vec<(usize, F)> {
    let mut result = Vec::with_capacity(lhs.len() + rhs.len());
    let mut lhs_index = 0;
    let mut rhs_index = 0;

    while lhs_index < lhs.len() || rhs_index < rhs.len() {
        match (lhs.get(lhs_index), rhs.get(rhs_index)) {
            (Some(&(lhs_degree, lhs_coeff)), Some(&(rhs_degree, rhs_coeff))) => {
                match lhs_degree.cmp(&rhs_degree) {
                    Ordering::Less => {
                        if !lhs_coeff.is_zero() {
                            result.push((lhs_degree, lhs_coeff));
                        }
                        lhs_index += 1;
                    },
                    Ordering::Equal => {
                        let coeff = lhs_coeff + map_rhs(rhs_coeff);
                        if !coeff.is_zero() {
                            result.push((lhs_degree, coeff));
                        }
                        lhs_index += 1;
                        rhs_index += 1;
                    },
                    Ordering::Greater => {
                        let coeff = map_rhs(rhs_coeff);
                        if !coeff.is_zero() {
                            result.push((rhs_degree, coeff));
                        }
                        rhs_index += 1;
                    },
                }
            },
            (Some(&(degree, coeff)), None) => {
                if !coeff.is_zero() {
                    result.push((degree, coeff));
                }
                lhs_index += 1;
            },
            (None, Some(&(degree, coeff))) => {
                let coeff = map_rhs(coeff);
                if !coeff.is_zero() {
                    result.push((degree, coeff));
                }
                rhs_index += 1;
            },
            (None, None) => break,
        }
    }

    result
}

impl<F: Field> fmt::Debug for SparsePolynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        for (i, coeff) in self.coeffs.iter().filter(|(_, c)| !c.is_zero()) {
            if *i == 0 {
                write!(f, "\n{coeff:?}")?;
            } else if *i == 1 {
                write!(f, " + \n{coeff:?} * x")?;
            } else {
                write!(f, " + \n{coeff:?} * x^{i}")?;
            }
        }
        Ok(())
    }
}

impl<F: Field> Deref for SparsePolynomial<F> {
    type Target = [(usize, F)];

    fn deref(&self) -> &[(usize, F)] {
        &self.coeffs
    }
}

impl<F: Field> DerefMut for SparsePolynomial<F> {
    fn deref_mut(&mut self) -> &mut [(usize, F)] {
        &mut self.coeffs
    }
}

impl<F: Field> Polynomial<F> for SparsePolynomial<F> {
    type Point = F;

    /// Returns the degree of the polynomial.
    fn degree(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            assert!(self.coeffs.last().is_some_and(|(_, c)| !c.is_zero()));
            self.coeffs.last().unwrap().0
        }
    }

    /// Evaluates `self` at the given `point` in the field.
    fn evaluate(&self, point: &F) -> F {
        if self.is_zero() {
            return F::zero();
        }

        // We need floor(log2(deg)) + 1 powers, starting from the 0th power p^2^0 = p
        let num_powers = 0usize.leading_zeros() - self.degree().leading_zeros();
        let mut powers_of_2 = Vec::with_capacity(num_powers as usize);

        let mut p = *point;
        powers_of_2.push(p);
        for _ in 1..num_powers {
            p.square_in_place();
            powers_of_2.push(p);
        }
        // compute all coeff * point^{i} and then sum the results
        let total = self
            .coeffs
            .iter()
            .map(|(i, c)| {
                debug_assert_eq!(
                    F::pow_with_table(&powers_of_2[..], [*i as u64]).unwrap(),
                    point.pow([*i as u64]),
                    "pows not equal"
                );
                *c * F::pow_with_table(&powers_of_2[..], [*i as u64]).unwrap()
            })
            .sum();
        total
    }
}

impl<F: Field> Add for SparsePolynomial<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        &self + &other
    }
}

impl<'a, F: Field> Add<&'a SparsePolynomial<F>> for &SparsePolynomial<F> {
    type Output = SparsePolynomial<F>;

    fn add(self, other: &'a SparsePolynomial<F>) -> SparsePolynomial<F> {
        SparsePolynomial {
            coeffs: merge_coefficients(&self.coeffs, &other.coeffs, |coeff| coeff),
        }
    }
}

impl<'a, F: Field> AddAssign<&'a Self> for SparsePolynomial<F> {
    fn add_assign(&mut self, other: &'a Self) {
        let lhs = core::mem::take(&mut self.coeffs);
        self.coeffs = merge_coefficients(&lhs, &other.coeffs, |coeff| coeff);
    }
}

impl<'a, F: Field> AddAssign<(F, &'a Self)> for SparsePolynomial<F> {
    fn add_assign(&mut self, (f, other): (F, &'a Self)) {
        if f.is_zero() || other.is_zero() {
            return;
        }
        let lhs = core::mem::take(&mut self.coeffs);
        self.coeffs = merge_coefficients(&lhs, &other.coeffs, |coeff| f * coeff);
    }
}

impl<F: Field> Neg for SparsePolynomial<F> {
    type Output = Self;

    #[inline]
    fn neg(mut self) -> Self {
        for (_, coeff) in &mut self.coeffs {
            *coeff = -*coeff;
        }
        self
    }
}

impl<'a, F: Field> SubAssign<&'a Self> for SparsePolynomial<F> {
    #[inline]
    fn sub_assign(&mut self, other: &'a Self) {
        let lhs = core::mem::take(&mut self.coeffs);
        self.coeffs = merge_coefficients(&lhs, &other.coeffs, |coeff| -coeff);
    }
}

impl<F: Field> Mul<F> for &SparsePolynomial<F> {
    type Output = SparsePolynomial<F>;

    #[inline]
    fn mul(self, elem: F) -> SparsePolynomial<F> {
        if self.is_zero() || elem.is_zero() {
            SparsePolynomial::zero()
        } else {
            let mut result = self.clone();
            cfg_iter_mut!(result).for_each(|e| {
                e.1 *= elem;
            });
            result
        }
    }
}

impl<F: Field> Zero for SparsePolynomial<F> {
    /// Returns the zero polynomial.
    fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Checks if the given polynomial is zero.
    fn is_zero(&self) -> bool {
        self.coeffs.is_empty() || self.coeffs.iter().all(|(_, c)| c.is_zero())
    }
}

impl<F: Field> SparsePolynomial<F> {
    /// Constructs a new polynomial from a list of coefficients.
    pub fn from_coefficients_slice(coeffs: &[(usize, F)]) -> Self {
        Self::from_coefficients_vec(coeffs.to_vec())
    }

    /// Constructs a new polynomial from a list of coefficients.
    /// The function does not combine like terms and so multiple monomials
    /// of the same degree are ignored.
    pub fn from_coefficients_vec(mut coeffs: Vec<(usize, F)>) -> Self {
        // While there are zeros at the end of the coefficient vector, pop them off.
        while coeffs.last().is_some_and(|(_, c)| c.is_zero()) {
            coeffs.pop();
        }
        // Ensure that coeffs are in ascending order.
        coeffs.sort_by(|(c1, _), (c2, _)| c1.cmp(c2));
        // Check that either the coefficients vec is empty or that the last coeff is
        // non-zero.
        assert!(coeffs.last().map_or(true, |(_, c)| !c.is_zero()));

        Self { coeffs }
    }

    /// Perform a naive n^2 multiplication of `self` by `other`.
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            Self::zero()
        } else {
            let mut result = BTreeMap::new();
            for (i, self_coeff) in &self.coeffs {
                for (j, other_coeff) in &other.coeffs {
                    result
                        .entry(i + j)
                        .and_modify(|cur_coeff| *cur_coeff += *self_coeff * other_coeff)
                        .or_insert_with(|| *self_coeff * other_coeff);
                }
            }
            Self::from_coefficients_vec(result.into_iter().collect())
        }
    }

    /// Returns the quotient of the division of `self` of degree n by `other` of k values using an algorithm in O(nk)
    pub fn div(&self, other: &Self) -> DensePolynomial<F> {
        let dividend: DenseOrSparsePolynomial<'_, F> = self.into();
        let divisor: DenseOrSparsePolynomial<'_, F> = other.into();

        dividend.naive_div(&divisor).expect("division failed").0
    }
}

impl<F: FftField> SparsePolynomial<F> {
    /// Evaluate `self` over `domain`.
    pub fn evaluate_over_domain_by_ref<D: EvaluationDomain<F>>(
        &self,
        domain: D,
    ) -> Evaluations<F, D> {
        let poly: DenseOrSparsePolynomial<'_, F> = self.into();
        DenseOrSparsePolynomial::evaluate_over_domain(poly, domain)
    }

    /// Evaluate `self` over `domain`.
    pub fn evaluate_over_domain<D: EvaluationDomain<F>>(self, domain: D) -> Evaluations<F, D> {
        let poly: DenseOrSparsePolynomial<'_, F> = self.into();
        DenseOrSparsePolynomial::evaluate_over_domain(poly, domain)
    }
}

impl<F: Field> From<SparsePolynomial<F>> for DensePolynomial<F> {
    fn from(other: SparsePolynomial<F>) -> Self {
        let mut result = vec![F::zero(); other.degree() + 1];
        for (i, coeff) in other.coeffs {
            result[i] = coeff;
        }
        Self::from_coefficients_vec(result)
    }
}

impl<F: Field> From<DensePolynomial<F>> for SparsePolynomial<F> {
    fn from(dense_poly: DensePolynomial<F>) -> Self {
        Self::from_coefficients_vec(
            dense_poly
                .coeffs()
                .iter()
                .enumerate()
                .filter(|&(_, coeff)| !coeff.is_zero())
                .map(|(i, coeff)| (i, *coeff))
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        polynomial::Polynomial,
        univariate::{DensePolynomial, SparsePolynomial},
        EvaluationDomain, GeneralEvaluationDomain,
    };
    use ark_ff::{UniformRand, Zero};
    use ark_std::{cmp::max, ops::Mul, rand::Rng, test_rng, vec};
    use ark_test_curves::bls12_381::Fr;

    // probability of rand sparse polynomial having a particular coefficient be 0
    const ZERO_COEFF_PROBABILITY: f64 = 0.8f64;

    fn rand_sparse_poly<R: Rng>(degree: usize, rng: &mut R) -> SparsePolynomial<Fr> {
        // Initialize coeffs so that its guaranteed to have a x^{degree} term
        let mut coeffs = vec![(degree, Fr::rand(rng))];
        for i in 0..degree {
            if !rng.gen_bool(ZERO_COEFF_PROBABILITY) {
                coeffs.push((i, Fr::rand(rng)));
            }
        }
        SparsePolynomial::from_coefficients_vec(coeffs)
    }

    #[test]
    fn evaluate_at_point() {
        let mut rng = test_rng();
        // Test evaluation at point by comparing against DensePolynomial
        for degree in 0..60 {
            let sparse_poly = rand_sparse_poly(degree, &mut rng);
            let dense_poly: DensePolynomial<Fr> = sparse_poly.clone().into();
            let pt = Fr::rand(&mut rng);
            assert_eq!(sparse_poly.evaluate(&pt), dense_poly.evaluate(&pt));
        }
    }

    #[test]
    fn add_polynomial() {
        // Test adding polynomials by comparing against dense polynomial
        let mut rng = test_rng();
        for degree_a in 0..20 {
            let sparse_poly_a = rand_sparse_poly(degree_a, &mut rng);
            let dense_poly_a: DensePolynomial<Fr> = sparse_poly_a.clone().into();
            for degree_b in 0..20 {
                let sparse_poly_b = rand_sparse_poly(degree_b, &mut rng);
                let dense_poly_b: DensePolynomial<Fr> = sparse_poly_b.clone().into();

                // Test Add trait
                let sparse_sum = sparse_poly_a.clone() + sparse_poly_b.clone();
                assert_eq!(
                    sparse_sum.degree(),
                    max(degree_a, degree_b),
                    "degree_a = {}, degree_b = {}",
                    degree_a,
                    degree_b
                );
                let actual_dense_sum: DensePolynomial<Fr> = sparse_sum.into();
                let expected_dense_sum = dense_poly_a.clone() + dense_poly_b;
                assert_eq!(
                    actual_dense_sum, expected_dense_sum,
                    "degree_a = {}, degree_b = {}",
                    degree_a, degree_b
                );
                // Test AddAssign Trait
                let mut sparse_add_assign_sum = sparse_poly_a.clone();
                sparse_add_assign_sum += &sparse_poly_b;
                let actual_add_assign_dense_sum: DensePolynomial<Fr> = sparse_add_assign_sum.into();
                assert_eq!(
                    actual_add_assign_dense_sum, expected_dense_sum,
                    "degree_a = {}, degree_b = {}",
                    degree_a, degree_b
                );
            }
        }
    }

    #[test]
    fn polynomial_additive_identity() {
        // Test adding polynomials with its negative equals 0
        let mut rng = test_rng();
        for degree in 0..70 {
            // Test with Neg trait
            let sparse_poly = rand_sparse_poly(degree, &mut rng);
            let neg = -sparse_poly.clone();
            assert!((sparse_poly + neg).is_zero());

            // Test with SubAssign trait
            let sparse_poly = rand_sparse_poly(degree, &mut rng);
            let mut result = sparse_poly.clone();
            result -= &sparse_poly;
            assert!(result.is_zero());
        }
    }

    #[test]
    fn add_scaled_and_sub_assign_match_dense() {
        let mut rng = test_rng();
        for degree_a in 0..20 {
            let sparse_a = rand_sparse_poly(degree_a, &mut rng);
            let dense_a: DensePolynomial<Fr> = sparse_a.clone().into();
            for degree_b in 0..20 {
                let sparse_b = rand_sparse_poly(degree_b, &mut rng);
                let dense_b: DensePolynomial<Fr> = sparse_b.clone().into();

                let mut sparse_difference = sparse_a.clone();
                sparse_difference -= &sparse_b;
                let mut dense_difference = dense_a.clone();
                dense_difference -= &dense_b;
                assert_eq!(DensePolynomial::from(sparse_difference), dense_difference);

                let scalar = Fr::rand(&mut rng);
                let mut sparse_scaled_sum = sparse_a.clone();
                sparse_scaled_sum += (scalar, &sparse_b);
                let mut dense_scaled_sum = dense_a.clone();
                dense_scaled_sum += (scalar, &dense_b);
                assert_eq!(DensePolynomial::from(sparse_scaled_sum), dense_scaled_sum);
            }
        }
    }

    #[test]
    fn mul_random_element() {
        let rng = &mut test_rng();
        for degree in 0..20 {
            let a = rand_sparse_poly(degree, rng);
            let e = Fr::rand(rng);
            assert_eq!(
                &a * e,
                a.mul(&SparsePolynomial::from_coefficients_slice(&[(0, e)]))
            )
        }
    }

    #[test]
    fn mul_polynomial() {
        // Test multiplying polynomials over their domains, and over the native
        // representation. The expected result is obtained by comparing against
        // dense polynomial
        let mut rng = test_rng();
        for degree_a in 0..20 {
            let sparse_poly_a = rand_sparse_poly(degree_a, &mut rng);
            let dense_poly_a: DensePolynomial<Fr> = sparse_poly_a.clone().into();
            for degree_b in 0..20 {
                let sparse_poly_b = rand_sparse_poly(degree_b, &mut rng);
                let dense_poly_b: DensePolynomial<Fr> = sparse_poly_b.clone().into();

                // Test multiplying the polynomials over their native representation
                let sparse_prod = sparse_poly_a.mul(&sparse_poly_b);
                assert_eq!(
                    sparse_prod.degree(),
                    degree_a + degree_b,
                    "degree_a = {}, degree_b = {}",
                    degree_a,
                    degree_b
                );
                let dense_prod = dense_poly_a.naive_mul(&dense_poly_b);
                assert_eq!(sparse_prod.degree(), dense_prod.degree());
                assert_eq!(
                    sparse_prod,
                    SparsePolynomial::<Fr>::from(dense_prod),
                    "degree_a = {}, degree_b = {}",
                    degree_a,
                    degree_b
                );

                // Test multiplying the polynomials over their evaluations and interpolating
                let domain = GeneralEvaluationDomain::new(sparse_prod.degree() + 1).unwrap();
                let poly_a_evals = sparse_poly_a.evaluate_over_domain_by_ref(domain);
                let poly_b_evals = sparse_poly_b.evaluate_over_domain_by_ref(domain);
                let poly_prod_evals = sparse_prod.evaluate_over_domain_by_ref(domain);
                assert_eq!(poly_a_evals.mul(&poly_b_evals), poly_prod_evals);
            }
        }
    }

    #[test]
    fn div_polynomial() {
        let mut rng = test_rng();
        for degree_a in 0..10 {
            let sparse_poly_a = rand_sparse_poly(degree_a, &mut rng);
            let dense_poly_a: DensePolynomial<Fr> = sparse_poly_a.clone().into();
            for degree_b in 0..degree_a {
                let sparse_poly_b = rand_sparse_poly(degree_b, &mut rng);
                let dense_poly_b: DensePolynomial<Fr> = sparse_poly_b.clone().into();

                // Test dividing the polynomials over their native representation
                let sparse_quotient = sparse_poly_a.div(&sparse_poly_b);
                assert_eq!(
                    sparse_quotient.degree(),
                    degree_a - degree_b,
                    "degree_a  = {}, degree_b = {}, degree_q = {}",
                    degree_a - degree_b,
                    degree_b,
                    sparse_quotient.degree(),
                );

                // Test that both dense and sparse division will return the same value
                // Since the FFT division is tested in the dense.rs, we then know this division is valid too
                // (we are over FFT fields so dense div will be FFT)
                let dense_quotient = &dense_poly_a / &dense_poly_b;
                assert_eq!(sparse_quotient.degree(), dense_quotient.degree());
                assert_eq!(
                    sparse_quotient,
                    dense_quotient,
                    "sparse quotient different from dense quotient for the same division! sparse {:?}, dense {:?}",
                    sparse_quotient,
                    dense_quotient,
                );
            }
        }
    }

    #[test]
    fn evaluate_over_domain() {
        // Test that polynomial evaluation over a domain, and interpolation returns the
        // same poly.
        let mut rng = test_rng();
        for poly_degree_dim in 0..5 {
            let poly_degree = (1 << poly_degree_dim) - 1;
            let sparse_poly = rand_sparse_poly(poly_degree, &mut rng);

            for domain_dim in poly_degree_dim..(poly_degree_dim + 2) {
                let domain_size = 1 << domain_dim;
                let domain = GeneralEvaluationDomain::new(domain_size).unwrap();

                let sparse_evals = sparse_poly.evaluate_over_domain_by_ref(domain);

                // Test interpolation works, by checking against DensePolynomial
                let dense_poly: DensePolynomial<Fr> = sparse_poly.clone().into();
                let dense_evals = dense_poly.clone().evaluate_over_domain(domain);
                assert_eq!(
                    sparse_evals.clone().interpolate(),
                    dense_evals.clone().interpolate(),
                    "poly_degree_dim = {}, domain_dim = {}",
                    poly_degree_dim,
                    domain_dim
                );
                assert_eq!(
                    sparse_evals.interpolate(),
                    dense_poly,
                    "poly_degree_dim = {}, domain_dim = {}",
                    poly_degree_dim,
                    domain_dim
                );
                // Consistency check that the dense polynomials interpolation is correct.
                assert_eq!(
                    dense_evals.interpolate(),
                    dense_poly,
                    "poly_degree_dim = {}, domain_dim = {}",
                    poly_degree_dim,
                    domain_dim
                );
            }
        }
    }

    #[test]
    fn evaluate_over_small_domain() {
        // Test that polynomial evaluation over a domain, and interpolation returns the
        // same poly.
        let mut rng = test_rng();
        for poly_degree_dim in 1..5 {
            let poly_degree = (1 << poly_degree_dim) - 1;
            let sparse_poly = rand_sparse_poly(poly_degree, &mut rng);

            for domain_dim in 0..poly_degree_dim {
                let domain_size = 1 << domain_dim;
                let domain = GeneralEvaluationDomain::new(domain_size).unwrap();

                let sparse_evals = sparse_poly.evaluate_over_domain_by_ref(domain);

                // Test that sparse evaluation and dense evaluation agree
                let dense_poly: DensePolynomial<Fr> = sparse_poly.clone().into();
                let dense_evals = dense_poly.clone().evaluate_over_domain(domain);
                assert_eq!(
                    sparse_evals, dense_evals,
                    "poly_degree_dim = {}, domain_dim = {}",
                    poly_degree_dim, domain_dim
                );

                // Test interpolation works, by checking that interpolated polynomial agrees with the original on the domain
                let (_q, r) = (dense_poly.clone() + -sparse_evals.interpolate())
                    .divide_by_vanishing_poly(domain);
                assert_eq!(
                    r,
                    DensePolynomial::<Fr>::zero(),
                    "poly_degree_dim = {}, domain_dim = {}",
                    poly_degree_dim,
                    domain_dim
                );

                // Consistency check that the dense polynomials interpolation is correct.
                let (_q, r) = (dense_poly.clone() + -dense_evals.interpolate())
                    .divide_by_vanishing_poly(domain);
                assert_eq!(
                    r,
                    DensePolynomial::<Fr>::zero(),
                    "poly_degree_dim = {}, domain_dim = {}",
                    poly_degree_dim,
                    domain_dim
                );
            }
        }
    }
}
