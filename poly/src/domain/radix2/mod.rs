//! This module defines `Radix2EvaluationDomain`, an `EvaluationDomain`
//! for performing various kinds of polynomial arithmetic on top of
//! fields that are FFT-friendly. `Radix2EvaluationDomain` supports
//! FFTs of size at most `2^F::TWO_ADICITY`.

pub use crate::domain::utils::Elements;
use crate::domain::{DomainCoeff, EvaluationDomain};
use ark_ff::FftField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{fmt, vec::*};

mod fft;

/// Factor that determines if a the degree aware FFT should be called.
const DEGREE_AWARE_FFT_THRESHOLD_FACTOR: usize = 1 << 2;

/// Defines a domain over which finite field (I)FFTs can be performed. Works
/// only for fields that have a large multiplicative subgroup of size that is
/// a power-of-2.
#[derive(Copy, Clone, Hash, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Radix2EvaluationDomain<F: FftField> {
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
    /// Constant coefficient for the vanishing polynomial.
    /// Equals `self.offset^self.size`.
    pub offset_pow_size: F,
}

impl<F: FftField> fmt::Debug for Radix2EvaluationDomain<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Radix-2 multiplicative subgroup of size {}", self.size)
    }
}

impl<F: FftField> EvaluationDomain<F> for Radix2EvaluationDomain<F> {
    type Elements = Elements<F>;

    /// Construct a domain that is large enough for evaluations of a polynomial
    /// having `num_coeffs` coefficients.
    fn new(num_coeffs: usize) -> Option<Self> {
        let size = if num_coeffs.is_power_of_two() {
            num_coeffs
        } else {
            num_coeffs.checked_next_power_of_two()?
        } as u64;
        let log_size_of_group = size.trailing_zeros();

        // libfqfft uses > https://github.com/scipr-lab/libfqfft/blob/e0183b2cef7d4c5deb21a6eaf3fe3b586d738fe0/libfqfft/evaluation_domain/domains/basic_radix2_domain.tcc#L33
        if log_size_of_group > F::TWO_ADICITY {
            return None;
        }

        // Compute the generator for the multiplicative subgroup.
        // It should be the 2^(log_size_of_group) root of unity.
        let group_gen = F::get_root_of_unity(size)?;
        // Check that it is indeed the 2^(log_size_of_group) root of unity.
        debug_assert_eq!(group_gen.pow([size]), F::one());
        let size_as_field_element = F::from(size);
        let size_inv = size_as_field_element.inverse()?;

        Some(Radix2EvaluationDomain {
            size,
            log_size_of_group,
            size_as_field_element,
            size_inv,
            group_gen,
            group_gen_inv: group_gen.inverse()?,
            offset: F::one(),
            offset_inv: F::one(),
            offset_pow_size: F::one(),
        })
    }

    fn get_coset(&self, offset: F) -> Option<Self> {
        Some(Radix2EvaluationDomain {
            offset,
            offset_inv: offset.inverse()?,
            offset_pow_size: offset.pow([self.size]),
            ..*self
        })
    }

    fn compute_size_of_domain(num_coeffs: usize) -> Option<usize> {
        let size = num_coeffs.checked_next_power_of_two()?;
        if size.trailing_zeros() > F::TWO_ADICITY {
            None
        } else {
            Some(size)
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
    fn coset_offset(&self) -> F {
        self.offset
    }

    #[inline]
    fn coset_offset_inv(&self) -> F {
        self.offset_inv
    }

    #[inline]
    fn coset_offset_pow_size(&self) -> F {
        self.offset_pow_size
    }

    #[inline]
    fn fft_in_place<T: DomainCoeff<F>>(&self, coeffs: &mut Vec<T>) {
        if coeffs.len() * DEGREE_AWARE_FFT_THRESHOLD_FACTOR <= self.size() {
            self.degree_aware_fft_in_place(coeffs);
        } else {
            coeffs.resize(self.size(), T::zero());
            self.in_order_fft_in_place(coeffs);
        }
    }

    #[inline]
    fn ifft_in_place<T: DomainCoeff<F>>(&self, evals: &mut Vec<T>) {
        evals.resize(self.size(), T::zero());
        self.in_order_ifft_in_place(&mut *evals);
    }

    /// Return an iterator over the elements of the domain.
    fn elements(&self) -> Elements<F> {
        Elements {
            cur_elem: self.offset,
            cur_pow: 0,
            size: self.size,
            group_gen: self.group_gen,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::DEGREE_AWARE_FFT_THRESHOLD_FACTOR;
    use crate::{
        polynomial::{univariate::*, DenseUVPolynomial, Polynomial},
        EvaluationDomain, Radix2EvaluationDomain,
    };
    use ark_ff::{FftField, Field, One, UniformRand, Zero};
    use ark_std::{collections::BTreeSet, rand::Rng, test_rng};
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn vanishing_polynomial_evaluation() {
        let rng = &mut test_rng();
        for coeffs in 0..10 {
            let domain = Radix2EvaluationDomain::<Fr>::new(coeffs).unwrap();
            let coset_domain = domain.get_coset(Fr::GENERATOR).unwrap();
            let z = domain.vanishing_polynomial();
            let z_coset = coset_domain.vanishing_polynomial();
            for _ in 0..100 {
                let point: Fr = rng.gen();
                assert_eq!(
                    z.evaluate(&point),
                    domain.evaluate_vanishing_polynomial(point)
                );
                assert_eq!(
                    z_coset.evaluate(&point),
                    coset_domain.evaluate_vanishing_polynomial(point)
                );
            }
        }
    }

    #[test]
    fn vanishing_polynomial_vanishes_on_domain() {
        for coeffs in 0..1000 {
            let domain = Radix2EvaluationDomain::<Fr>::new(coeffs).unwrap();
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

    #[test]
    fn filter_polynomial_test() {
        for log_domain_size in 1..=4 {
            let domain_size = 1 << log_domain_size;
            let domain = Radix2EvaluationDomain::<Fr>::new(domain_size).unwrap();
            for log_subdomain_size in 1..=log_domain_size {
                let subdomain_size = 1 << log_subdomain_size;
                let subdomain = Radix2EvaluationDomain::<Fr>::new(subdomain_size).unwrap();

                // Obtain all possible offsets of `subdomain` within `domain`.
                let mut possible_offsets = vec![Fr::one()];
                let domain_generator = domain.group_gen();

                let mut offset = domain_generator;
                let subdomain_generator = subdomain.group_gen();
                while offset != subdomain_generator {
                    possible_offsets.push(offset);
                    offset *= domain_generator;
                }

                assert_eq!(possible_offsets.len(), domain_size / subdomain_size);

                // Get all possible cosets of `subdomain` within `domain`.
                let cosets = possible_offsets
                    .iter()
                    .map(|offset| subdomain.get_coset(*offset).unwrap());

                for coset in cosets {
                    let coset_elements = coset.elements().collect::<BTreeSet<_>>();
                    let filter_poly = domain.filter_polynomial(&coset);
                    assert_eq!(filter_poly.degree(), domain_size - subdomain_size);
                    for element in domain.elements() {
                        let evaluation = domain.evaluate_filter_polynomial(&coset, element);
                        assert_eq!(evaluation, filter_poly.evaluate(&element));
                        if coset_elements.contains(&element) {
                            assert_eq!(evaluation, Fr::one())
                        } else {
                            assert_eq!(evaluation, Fr::zero())
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn size_of_elements() {
        for coeffs in 1..10 {
            let size = 1 << coeffs;
            let domain = Radix2EvaluationDomain::<Fr>::new(size).unwrap();
            let domain_size = domain.size();
            assert_eq!(domain_size, domain.elements().count());
        }
    }

    #[test]
    fn elements_contents() {
        for coeffs in 1..10 {
            let size = 1 << coeffs;
            let domain = Radix2EvaluationDomain::<Fr>::new(size).unwrap();
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

    /// Test that lagrange interpolation for a random polynomial at a random
    /// point works.
    #[test]
    fn non_systematic_lagrange_coefficients_test() {
        for domain_dim in 1..10 {
            let domain_size = 1 << domain_dim;
            let domain = Radix2EvaluationDomain::<Fr>::new(domain_size).unwrap();
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
            let domain = Radix2EvaluationDomain::<Fr>::new(domain_size).unwrap();
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
    fn test_fft_correctness() {
        // Tests that the ffts output the correct result.
        // This assumes a correct polynomial evaluation at point procedure.
        // It tests consistency of FFT/IFFT, and coset_fft/coset_ifft,
        // along with testing that each individual evaluation is correct.

        // Runs in time O(degree^2)
        let log_degree = 5;
        let degree = 1 << log_degree;
        let rand_poly = DensePolynomial::<Fr>::rand(degree - 1, &mut test_rng());

        for log_domain_size in log_degree..(log_degree + 2) {
            let domain_size = 1 << log_domain_size;
            let domain = Radix2EvaluationDomain::<Fr>::new(domain_size).unwrap();
            let coset_domain =
                Radix2EvaluationDomain::<Fr>::new_coset(domain_size, Fr::GENERATOR).unwrap();
            let poly_evals = domain.fft(&rand_poly.coeffs);
            let poly_coset_evals = coset_domain.fft(&rand_poly.coeffs);

            for (i, (x, coset_x)) in domain.elements().zip(coset_domain.elements()).enumerate() {
                assert_eq!(poly_evals[i], rand_poly.evaluate(&x));
                assert_eq!(poly_coset_evals[i], rand_poly.evaluate(&coset_x));
            }

            let rand_poly_from_subgroup =
                DensePolynomial::from_coefficients_vec(domain.ifft(&poly_evals));
            let rand_poly_from_coset =
                DensePolynomial::from_coefficients_vec(coset_domain.ifft(&poly_coset_evals));

            assert_eq!(
                rand_poly, rand_poly_from_subgroup,
                "degree = {}, domain size = {}",
                degree, domain_size
            );
            assert_eq!(
                rand_poly, rand_poly_from_coset,
                "degree = {}, domain size = {}",
                degree, domain_size
            );
        }
    }

    #[test]
    fn degree_aware_fft_correctness() {
        // Test that the degree aware FFT (O(n log d)) matches the regular FFT (O(n log n)).
        let num_coeffs = 1 << 5;
        let rand_poly = DensePolynomial::<Fr>::rand(num_coeffs - 1, &mut test_rng());
        let domain_size = num_coeffs * DEGREE_AWARE_FFT_THRESHOLD_FACTOR;
        let domain = Radix2EvaluationDomain::<Fr>::new(domain_size).unwrap();
        let coset_domain = domain.get_coset(Fr::GENERATOR).unwrap();

        let deg_aware_fft_evals = domain.fft(&rand_poly);
        let coset_deg_aware_fft_evals = coset_domain.fft(&rand_poly);

        for (i, (x, coset_x)) in domain.elements().zip(coset_domain.elements()).enumerate() {
            assert_eq!(deg_aware_fft_evals[i], rand_poly.evaluate(&x));
            assert_eq!(coset_deg_aware_fft_evals[i], rand_poly.evaluate(&coset_x));
        }
    }

    #[test]
    fn test_roots_of_unity() {
        // Tests that the roots of unity result is the same as domain.elements()
        let max_degree = 10;
        for log_domain_size in 0..max_degree {
            let domain_size = 1 << log_domain_size;
            let domain = Radix2EvaluationDomain::<Fr>::new(domain_size).unwrap();
            let actual_roots = domain.roots_of_unity(domain.group_gen);
            for &value in &actual_roots {
                assert!(domain.evaluate_vanishing_polynomial(value).is_zero());
            }
            let expected_roots_elements = domain.elements();
            for (expected, &actual) in expected_roots_elements.zip(&actual_roots) {
                assert_eq!(expected, actual);
            }
            assert_eq!(actual_roots.len(), domain_size / 2);
        }
    }

    #[test]
    #[cfg(feature = "parallel")]
    fn parallel_fft_consistency() {
        use ark_std::{test_rng, vec::*};
        use ark_test_curves::bls12_381::Fr;

        // This implements the Cooley-Turkey FFT, derived from libfqfft
        // The libfqfft implementation uses pseudocode from [CLRS 2n Ed, pp. 864].
        fn serial_radix2_fft(a: &mut [Fr], omega: Fr, log_n: u32) {
            use ark_std::convert::TryFrom;
            let n = u32::try_from(a.len())
                .expect("cannot perform FFTs larger on vectors of len > (1 << 32)");
            assert_eq!(n, 1 << log_n);

            // swap coefficients in place
            for k in 0..n {
                let rk = crate::domain::utils::bitreverse(k, log_n);
                if k < rk {
                    a.swap(rk as usize, k as usize);
                }
            }

            let mut m = 1;
            for _i in 1..=log_n {
                // w_m is 2^i-th root of unity
                let w_m = omega.pow([(n / (2 * m)) as u64]);

                let mut k = 0;
                while k < n {
                    // w = w_m^j at the start of every loop iteration
                    let mut w = Fr::one();
                    for j in 0..m {
                        let mut t = a[(k + j + m) as usize];
                        t *= w;
                        let mut tmp = a[(k + j) as usize];
                        tmp -= t;
                        a[(k + j + m) as usize] = tmp;
                        a[(k + j) as usize] += t;
                        w *= &w_m;
                    }

                    k += 2 * m;
                }

                m *= 2;
            }
        }

        fn serial_radix2_ifft(a: &mut [Fr], omega: Fr, log_n: u32) {
            serial_radix2_fft(a, omega.inverse().unwrap(), log_n);
            let domain_size_inv = Fr::from(a.len() as u64).inverse().unwrap();
            for coeff in a.iter_mut() {
                *coeff *= Fr::from(domain_size_inv);
            }
        }

        fn serial_radix2_coset_fft(a: &mut [Fr], omega: Fr, log_n: u32) {
            let coset_shift = Fr::GENERATOR;
            let mut cur_pow = Fr::one();
            for coeff in a.iter_mut() {
                *coeff *= cur_pow;
                cur_pow *= coset_shift;
            }
            serial_radix2_fft(a, omega, log_n);
        }

        fn serial_radix2_coset_ifft(a: &mut [Fr], omega: Fr, log_n: u32) {
            serial_radix2_ifft(a, omega, log_n);
            let coset_shift = Fr::GENERATOR.inverse().unwrap();
            let mut cur_pow = Fr::one();
            for coeff in a.iter_mut() {
                *coeff *= cur_pow;
                cur_pow *= coset_shift;
            }
        }

        fn test_consistency<R: Rng>(rng: &mut R, max_coeffs: u32) {
            for _ in 0..5 {
                for log_d in 0..max_coeffs {
                    let d = 1 << log_d;

                    let expected_poly = (0..d).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                    let mut expected_vec = expected_poly.clone();
                    let mut actual_vec = expected_vec.clone();

                    let domain = Radix2EvaluationDomain::new(d).unwrap();
                    let coset_domain = domain.get_coset(Fr::GENERATOR).unwrap();

                    serial_radix2_fft(&mut expected_vec, domain.group_gen, log_d);
                    domain.fft_in_place(&mut actual_vec);
                    assert_eq!(expected_vec, actual_vec);

                    serial_radix2_ifft(&mut expected_vec, domain.group_gen, log_d);
                    domain.ifft_in_place(&mut actual_vec);
                    assert_eq!(expected_vec, actual_vec);
                    assert_eq!(expected_vec, expected_poly);

                    serial_radix2_coset_fft(&mut expected_vec, domain.group_gen, log_d);
                    coset_domain.fft_in_place(&mut actual_vec);
                    assert_eq!(expected_vec, actual_vec);

                    serial_radix2_coset_ifft(&mut expected_vec, domain.group_gen, log_d);
                    coset_domain.ifft_in_place(&mut actual_vec);
                    assert_eq!(expected_vec, actual_vec);
                }
            }
        }

        let rng = &mut test_rng();

        test_consistency(rng, 10);
    }
}
