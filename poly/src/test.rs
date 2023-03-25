use crate::domain::*;
use ark_ff::{PrimeField, UniformRand};
use ark_std::test_rng;
use ark_test_curves::{
    bls12_381::{Fr, G1Projective},
    bn384_small_two_adicity::Fr as BNFr,
};
use crate::{
    EvaluationDomain,
    domain::general::GeneralEvaluationDomain, univariate::DensePolynomial,
};

// Simple test to showcase the usage of FFT and iFFT using
// ark-poly APIs.
#[test]
fn test_fft_example() {
    // Create a random polynomial of degree 3
    let coeffs = vec![Fr::from(1u8), Fr::from(2u8), Fr::from(3u8), Fr::from(4u8)];
    let poly = DensePolynomial {
        coeffs: coeffs.clone(),
    };
    let domain = GeneralEvaluationDomain::<Fr>::new(4).unwrap();

    // Compute the FFT of the evaluations
    let evals = domain.fft(&coeffs);

    // Compute the inverse FFT of the FFT
    let inv_fft = domain.ifft(&evals);

    // Convert the inverse FFT back into a polynomial
    let poly_again = DensePolynomial { coeffs: inv_fft };

    // Verify that the original and reconstructed polynomials match
    assert_eq!(poly, poly_again);
}

// Test multiplying various (low degree) polynomials together and
// comparing with naive evaluations.
#[test]
fn fft_composition() {
    fn test_fft_composition<
        F: PrimeField,
        T: DomainCoeff<F> + UniformRand + core::fmt::Debug + Eq,
        R: ark_std::rand::Rng,
        D: EvaluationDomain<F>,
    >(
        rng: &mut R,
        max_coeffs: usize,
    ) {
        for coeffs in 0..max_coeffs {
            let coeffs = 1 << coeffs;

            let domain = D::new(coeffs).unwrap();
            let coset_domain = domain.get_coset(F::GENERATOR).unwrap();

            let mut v = vec![];
            for _ in 0..coeffs {
                v.push(T::rand(rng));
            }
            // Fill up with zeros.
            v.resize(domain.size(), T::zero());
            let mut v2 = v.clone();

            domain.ifft_in_place(&mut v2);
            domain.fft_in_place(&mut v2);
            assert_eq!(v, v2, "ifft(fft(.)) != iden");

            domain.fft_in_place(&mut v2);
            domain.ifft_in_place(&mut v2);
            assert_eq!(v, v2, "fft(ifft(.)) != iden");

            coset_domain.ifft_in_place(&mut v2);
            coset_domain.fft_in_place(&mut v2);
            assert_eq!(v, v2, "fft(ifft(.)) != iden");

            coset_domain.fft_in_place(&mut v2);
            coset_domain.ifft_in_place(&mut v2);
            assert_eq!(v, v2, "ifft(fft(.)) != iden");
        }
    }

    let rng = &mut test_rng();

    test_fft_composition::<Fr, Fr, _, GeneralEvaluationDomain<Fr>>(rng, 10);
    test_fft_composition::<Fr, G1Projective, _, GeneralEvaluationDomain<Fr>>(rng, 10);
    // This will result in a mixed-radix domain being used.
    test_fft_composition::<BNFr, BNFr, _, MixedRadixEvaluationDomain<_>>(rng, 12);
}
