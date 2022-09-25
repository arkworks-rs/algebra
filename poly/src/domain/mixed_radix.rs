//! This module contains a `MixedRadixEvaluationDomain` for
//! performing various kinds of polynomial arithmetic on top of
//! fields that are FFT-friendly but do not have high-enough
//! two-adicity to perform the FFT efficiently, i.e. the multiplicative
//! subgroup `G` generated by `F::TWO_ADIC_ROOT_OF_UNITY` is not large enough.
//! `MixedRadixEvaluationDomain` resolves
//! this issue by using a larger subgroup obtained by combining
//! `G` with another subgroup of size
//! `F::SMALL_SUBGROUP_BASE^(F::SMALL_SUBGROUP_BASE_ADICITY)`,
//! to obtain a subgroup generated by `F::LARGE_SUBGROUP_ROOT_OF_UNITY`.

pub use crate::domain::utils::Elements;
use crate::domain::{
    utils::{best_fft, bitreverse},
    DomainCoeff, EvaluationDomain,
};
use ark_ff::{fields::utils::k_adicity, FftField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{cmp::min, convert::TryFrom, fmt, vec::Vec};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Defines a domain over which finite field (I)FFTs can be performed. Works
/// only for fields that have a multiplicative subgroup of size that is
/// a power-of-2 and another small subgroup over a different base defined.
#[derive(Copy, Clone, Hash, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct MixedRadixEvaluationDomain<F: FftField> {
    /// The size of the domain.
    pub size: u64,
    /// `log_2(self.size)`.
    pub log_size_of_group: u32,
    /// Size of the domain as a field element.
    pub size_as_field_element: F,
    /// Inverse of the size in the field.
    pub size_inv: F,
    /// A generator of the subgroup.
    pub group_gen: F,
    /// Inverse of the generator of the subgroup.
    pub group_gen_inv: F,
    /// Offset that specifies the coset.
    pub offset: F,
    /// Inverse of the offset that specifies the coset.
    pub offset_inv: F,
}

impl<F: FftField> fmt::Debug for MixedRadixEvaluationDomain<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Mixed-radix multiplicative subgroup of size {}",
            self.size
        )
    }
}

impl<F: FftField> EvaluationDomain<F> for MixedRadixEvaluationDomain<F> {
    type Elements = Elements<F>;

    /// Construct a domain that is large enough for evaluations of a polynomial
    /// having `num_coeffs` coefficients.
    fn new(num_coeffs: usize) -> Option<Self> {
        // Compute the best size of our evaluation domain.
        Self::new_subgroup(best_mixed_domain_size::<F>(num_coeffs))
    }

    fn new_subgroup(subgroup_size: usize) -> Option<Self> {
        let size = subgroup_size as u64;
        let small_subgroup_base = F::SMALL_SUBGROUP_BASE?;

        // Compute the size of our evaluation domain
        let q = u64::from(small_subgroup_base);
        let q_adicity = k_adicity(q, size);
        let q_part = q.checked_pow(q_adicity)?;

        let two_adicity = k_adicity(2, size);
        let log_size_of_group = two_adicity;
        let two_part = 2u64.checked_pow(two_adicity)?;

        if size != q_part * two_part {
            return None;
        }

        // Compute the generator for the multiplicative subgroup.
        // It should be the num_coeffs root of unity.
        let group_gen = F::get_root_of_unity(size)?;
        // Check that it is indeed the requested root of unity.
        debug_assert_eq!(group_gen.pow([size]), F::one());
        let size_as_field_element = F::from(size);
        let size_inv = size_as_field_element.inverse()?;

        Some(MixedRadixEvaluationDomain {
            size,
            log_size_of_group,
            size_as_field_element,
            size_inv,
            group_gen,
            group_gen_inv: group_gen.inverse()?,
            offset: F::one(),
            offset_inv: F::one(),
        })
    }

    fn get_coset(&self, offset: F) -> Option<Self> {
        Some(MixedRadixEvaluationDomain {
            offset,
            offset_inv: offset.inverse()?,
            ..*self
        })
    }

    fn compute_size_of_domain(num_coeffs: usize) -> Option<usize> {
        let small_subgroup_base = F::SMALL_SUBGROUP_BASE?;

        // Compute the best size of our evaluation domain.
        let num_coeffs = best_mixed_domain_size::<F>(num_coeffs) as u64;

        let q = u64::from(small_subgroup_base);
        let q_adicity = k_adicity(q, num_coeffs);
        let q_part = q.checked_pow(q_adicity)?;

        let two_adicity = k_adicity(2, num_coeffs);
        let two_part = 2u64.checked_pow(two_adicity)?;

        if num_coeffs == q_part * two_part {
            Some(num_coeffs as usize)
        } else {
            None
        }
    }

    #[inline]
    fn size(&self) -> usize {
        usize::try_from(self.size).unwrap()
    }

    #[inline]
    fn log_size_of_group(&self) -> u64 {
        self.log_size_of_group as u64
    }

    #[inline]
    fn size_inv(&self) -> F {
        self.size_inv
    }

    #[inline]
    fn group_gen(&self) -> F {
        self.group_gen
    }

    #[inline]
    fn group_gen_inv(&self) -> F {
        self.group_gen_inv
    }

    #[inline]
    fn offset(&self) -> F {
        self.offset
    }

    #[inline]
    fn offset_inv(&self) -> F {
        self.offset_inv
    }

    #[inline]
    fn fft_in_place<T: DomainCoeff<F>>(&self, coeffs: &mut Vec<T>) {
        if !self.offset.is_one() {
            Self::distribute_powers(coeffs, self.offset);
        }
        coeffs.resize(self.size(), T::zero());
        best_fft(
            coeffs,
            self.group_gen,
            self.log_size_of_group,
            serial_mixed_radix_fft::<T, F>,
        )
    }

    #[inline]
    fn ifft_in_place<T: DomainCoeff<F>>(&self, evals: &mut Vec<T>) {
        evals.resize(self.size(), T::zero());
        best_fft(
            evals,
            self.group_gen_inv,
            self.log_size_of_group,
            serial_mixed_radix_fft::<T, F>,
        );
        if self.offset.is_one() {
            ark_std::cfg_iter_mut!(evals).for_each(|val| *val *= self.size_inv);
        } else {
            Self::distribute_powers_and_mul_by_const(evals, self.offset_inv, self.size_inv);
        }
    }

    fn vanishing_polynomial(&self) -> crate::univariate::SparsePolynomial<F> {
        let coeffs = vec![(0, -self.offset.pow([self.size])), (self.size(), F::one())];
        crate::univariate::SparsePolynomial::from_coefficients_vec(coeffs)
    }

    /// This evaluates the vanishing polynomial for this domain at tau.
    /// For multiplicative subgroups, this polynomial is `z(X) = X^self.size -
    /// 1`.
    fn evaluate_vanishing_polynomial(&self, tau: F) -> F {
        tau.pow([self.size]) - self.offset.pow([self.size])
    }

    /// Returns the `i`-th element of the domain, where elements are ordered by
    /// their power of the generator which they correspond to.
    /// e.g. the `i`-th element is g^i
    fn element(&self, i: usize) -> F {
        // TODO: Consider precomputed exponentiation tables if we need this to be
        // faster.
        self.offset * self.group_gen.pow([i as u64])
    }

    /// Return an iterator over the elements of the domain.
    fn elements(&self) -> Elements<F> {
        Elements {
            cur_elem: F::one(),
            cur_pow: 0,
            size: self.size,
            group_gen: self.group_gen,
            offset: self.offset,
        }
    }
}

fn mixed_radix_fft_permute(
    two_adicity: u32,
    q_adicity: u32,
    q: usize,
    n: usize,
    mut i: usize,
) -> usize {
    // This is the permutation obtained by splitting into 2 groups two_adicity times
    // and then q groups q_adicity many times. It can be efficiently described
    // as follows i = 2^0 b_0 + 2^1 b_1 + ... + 2^{two_adicity - 1}
    // b_{two_adicity - 1} + 2^two_adicity ( x_0 + q^1 x_1 + .. +
    // q^{q_adicity-1} x_{q_adicity-1}) We want to return
    // j = b_0 (n/2) + b_1 (n/ 2^2) + ... + b_{two_adicity-1} (n/ 2^two_adicity)
    // + x_0 (n / 2^two_adicity / q) + .. + x_{q_adicity-1} (n / 2^two_adicity /
    // q^q_adicity)
    let mut res = 0;
    let mut shift = n;

    for _ in 0..two_adicity {
        shift /= 2;
        res += (i % 2) * shift;
        i /= 2;
    }

    for _ in 0..q_adicity {
        shift /= q;
        res += (i % q) * shift;
        i /= q;
    }

    res
}

fn best_mixed_domain_size<F: FftField>(min_size: usize) -> usize {
    let mut best = usize::max_value();
    let small_subgroup_base_adicity = F::SMALL_SUBGROUP_BASE_ADICITY.unwrap();
    let small_subgroup_base = usize::try_from(F::SMALL_SUBGROUP_BASE.unwrap()).unwrap();

    for b in 0..=small_subgroup_base_adicity {
        let mut r = small_subgroup_base.pow(b);

        let mut two_adicity = 0;
        while r < min_size {
            r *= 2;
            two_adicity += 1;
        }

        if two_adicity <= F::TWO_ADICITY {
            best = min(best, r);
        }
    }

    best
}

pub(crate) fn serial_mixed_radix_fft<T: DomainCoeff<F>, F: FftField>(
    a: &mut [T],
    omega: F,
    two_adicity: u32,
) {
    // Conceptually, this FFT first splits into 2 sub-arrays two_adicity many times,
    // and then splits into q sub-arrays q_adicity many times.

    let n = a.len();
    let q = usize::try_from(F::SMALL_SUBGROUP_BASE.unwrap()).unwrap();
    let q_u64 = u64::from(F::SMALL_SUBGROUP_BASE.unwrap());
    let n_u64 = n as u64;

    let q_adicity = k_adicity(q_u64, n_u64);
    let q_part = q_u64.checked_pow(q_adicity).unwrap();
    let two_part = 2u64.checked_pow(two_adicity).unwrap();

    assert_eq!(n_u64, q_part * two_part);

    let mut m = 1; // invariant: m = 2^{s-1}

    if q_adicity > 0 {
        // If we're using the other radix, we have to do two things differently than in
        // the radix 2 case. 1. Applying the index permutation is a bit more
        // complicated. It isn't an involution (like it is in the radix 2 case)
        // so we need to remember which elements we've moved as we go along
        // and can't use the trick of just swapping when processing the first element of
        // a 2-cycle.
        //
        // 2. We need to do q_adicity many merge passes, each of which is a bit more
        // complicated than the specialized q=2 case.

        // Applying the permutation
        let mut seen = vec![false; n];
        for k in 0..n {
            let mut i = k;
            let mut a_i = a[i];
            while !seen[i] {
                let dest = mixed_radix_fft_permute(two_adicity, q_adicity, q, n, i);

                let a_dest = a[dest];
                a[dest] = a_i;

                seen[i] = true;

                a_i = a_dest;
                i = dest;
            }
        }

        let omega_q = omega.pow([(n / q) as u64]);
        let mut qth_roots = Vec::with_capacity(q);
        qth_roots.push(F::one());
        for i in 1..q {
            qth_roots.push(qth_roots[i - 1] * omega_q);
        }

        let mut terms = vec![T::zero(); q - 1];

        // Doing the q_adicity passes.
        for _ in 0..q_adicity {
            let w_m = omega.pow([(n / (q * m)) as u64]);
            let mut k = 0;
            while k < n {
                let mut w_j = F::one(); // w_j is omega_m ^ j
                for j in 0..m {
                    let base_term = a[k + j];
                    let mut w_j_i = w_j;
                    for i in 1..q {
                        terms[i - 1] = a[k + j + i * m];
                        terms[i - 1] *= w_j_i;
                        w_j_i *= w_j;
                    }

                    for i in 0..q {
                        a[k + j + i * m] = base_term;
                        for l in 1..q {
                            let mut tmp = terms[l - 1];
                            tmp *= qth_roots[(i * l) % q];
                            a[k + j + i * m] += tmp;
                        }
                    }

                    w_j *= w_m;
                }

                k += q * m;
            }
            m *= q;
        }
    } else {
        // swapping in place (from Storer's book)
        for k in 0..n {
            let rk = bitreverse(k as u32, two_adicity) as usize;
            if k < rk {
                a.swap(k, rk);
            }
        }
    }

    for _ in 0..two_adicity {
        // w_m is 2^s-th root of unity now
        let w_m = omega.pow([(n / (2 * m)) as u64]);

        let mut k = 0;
        while k < n {
            let mut w = F::one();
            for j in 0..m {
                let mut t = a[(k + m) + j];
                t *= w;
                a[(k + m) + j] = a[k + j];
                a[(k + m) + j] -= t;
                a[k + j] += t;
                w *= w_m;
            }
            k += 2 * m;
        }
        m *= 2;
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        polynomial::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial},
        EvaluationDomain, MixedRadixEvaluationDomain,
    };
    use ark_ff::{FftField, Field, One, UniformRand, Zero};
    use ark_std::{rand::Rng, test_rng};
    use ark_test_curves::bn384_small_two_adicity::Fq as Fr;

    #[test]
    fn vanishing_polynomial_evaluation() {
        let rng = &mut test_rng();
        for coeffs in 0..12 {
            let domain = MixedRadixEvaluationDomain::<Fr>::new(coeffs).unwrap();
            let coset_domain = domain.get_coset(Fr::GENERATOR).unwrap();
            let z = domain.vanishing_polynomial();
            let coset_z = coset_domain.vanishing_polynomial();
            for _ in 0..100 {
                let point: Fr = rng.gen();
                assert_eq!(
                    z.evaluate(&point),
                    domain.evaluate_vanishing_polynomial(point)
                );
                assert_eq!(
                    coset_z.evaluate(&point),
                    coset_domain.evaluate_vanishing_polynomial(point)
                );
            }
        }
    }

    #[test]
    fn vanishing_polynomial_vanishes_on_domain() {
        for coeffs in 0..1000 {
            let domain = MixedRadixEvaluationDomain::<Fr>::new(coeffs).unwrap();
            let z = domain.vanishing_polynomial();
            for point in domain.elements() {
                assert!(z.evaluate(&point).is_zero())
            }

            let coset_domain = domain.get_coset(Fr::GENERATOR).unwrap();
            let z = coset_domain.vanishing_polynomial();
            for point in coset_domain.elements() {
                assert!(z.evaluate(&point).is_zero())
            }
        }
    }

    /// Test that lagrange interpolation for a random polynomial at a random
    /// point works.
    #[test]
    fn non_systematic_lagrange_coefficients_test() {
        for domain_dim in 1..10 {
            let domain_size = 1 << domain_dim;
            let domain = MixedRadixEvaluationDomain::<Fr>::new(domain_size).unwrap();
            let coset_domain = domain.get_coset(Fr::GENERATOR).unwrap();
            // Get random pt + lagrange coefficients
            let rand_pt = Fr::rand(&mut test_rng());
            let lagrange_coeffs = domain.evaluate_all_lagrange_coefficients(rand_pt);
            let coset_lagrange_coeffs = coset_domain.evaluate_all_lagrange_coefficients(rand_pt);

            // Sample the random polynomial, evaluate it over the domain and the random
            // point.
            let rand_poly = DensePolynomial::<Fr>::rand(domain_size - 1, &mut test_rng());
            let poly_evals = domain.fft(rand_poly.coeffs());
            let coset_poly_evals = coset_domain.fft(rand_poly.coeffs());
            let actual_eval = rand_poly.evaluate(&rand_pt);

            // Do lagrange interpolation, and compare against the actual evaluation
            let mut interpolated_eval = Fr::zero();
            let mut coset_interpolated_eval = Fr::zero();
            for i in 0..domain_size {
                interpolated_eval += lagrange_coeffs[i] * poly_evals[i];
                coset_interpolated_eval += coset_lagrange_coeffs[i] * coset_poly_evals[i];
            }
            assert_eq!(actual_eval, interpolated_eval);
            assert_eq!(actual_eval, coset_interpolated_eval);
        }
    }

    /// Test that lagrange coefficients for a point in the domain is correct
    #[test]
    fn systematic_lagrange_coefficients_test() {
        // This runs in time O(N^2) in the domain size, so keep the domain dimension
        // low. We generate lagrange coefficients for each element in the domain.
        for domain_dim in 1..5 {
            let domain_size = 1 << domain_dim;
            let domain = MixedRadixEvaluationDomain::<Fr>::new(domain_size).unwrap();
            let coset_domain = domain.get_coset(Fr::GENERATOR).unwrap();
            for (i, (x, coset_x)) in domain.elements().zip(coset_domain.elements()).enumerate() {
                let lagrange_coeffs = domain.evaluate_all_lagrange_coefficients(x);
                let coset_lagrange_coeffs =
                    coset_domain.evaluate_all_lagrange_coefficients(coset_x);
                for (j, (y, coset_y)) in lagrange_coeffs
                    .into_iter()
                    .zip(coset_lagrange_coeffs)
                    .enumerate()
                {
                    // Lagrange coefficient for the evaluation point, which should be 1
                    if i == j {
                        assert_eq!(y, Fr::one());
                        assert_eq!(coset_y, Fr::one());
                    } else {
                        assert_eq!(y, Fr::zero());
                        assert_eq!(coset_y, Fr::zero());
                    }
                }
            }
        }
    }

    #[test]
    fn size_of_elements() {
        for coeffs in 1..12 {
            let size = 1 << coeffs;
            let domain = MixedRadixEvaluationDomain::<Fr>::new(size).unwrap();
            let domain_size = domain.size();
            assert_eq!(domain_size, domain.elements().count());
        }
    }

    #[test]
    fn elements_contents() {
        for coeffs in 1..12 {
            let size = 1 << coeffs;
            let domain = MixedRadixEvaluationDomain::<Fr>::new(size).unwrap();
            let offset = Fr::GENERATOR;
            let coset_domain = domain.get_coset(offset).unwrap();
            for (i, (x, coset_x)) in domain.elements().zip(coset_domain.elements()).enumerate() {
                assert_eq!(x, domain.group_gen.pow([i as u64]));
                assert_eq!(x, domain.element(i));
                assert_eq!(coset_x, offset * coset_domain.group_gen.pow([i as u64]));
                assert_eq!(coset_x, coset_domain.element(i));
            }
        }
    }

    #[test]
    #[cfg(feature = "parallel")]
    fn parallel_fft_consistency() {
        use super::serial_mixed_radix_fft;
        use crate::domain::utils::parallel_fft;
        use ark_ff::PrimeField;
        use ark_std::{test_rng, vec::Vec};
        use ark_test_curves::bn384_small_two_adicity::Fq as Fr;
        use core::cmp::min;

        fn test_consistency<F: PrimeField, R: Rng>(rng: &mut R, max_coeffs: u32) {
            for _ in 0..5 {
                for log_d in 0..max_coeffs {
                    let d = 1 << log_d;

                    let mut v1 = (0..d).map(|_| F::rand(rng)).collect::<Vec<_>>();
                    let mut v2 = v1.clone();

                    let domain = MixedRadixEvaluationDomain::new(v1.len()).unwrap();

                    for log_cpus in log_d..min(log_d + 1, 3) {
                        parallel_fft::<F, F>(
                            &mut v1,
                            domain.group_gen,
                            log_d,
                            log_cpus,
                            serial_mixed_radix_fft::<F, F>,
                        );
                        serial_mixed_radix_fft::<F, F>(&mut v2, domain.group_gen, log_d);

                        assert_eq!(v1, v2);
                    }
                }
            }
        }

        let rng = &mut test_rng();

        test_consistency::<Fr, _>(rng, 16);
    }
}
