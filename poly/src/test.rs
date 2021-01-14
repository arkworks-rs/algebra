use crate::domain::*;
use ark_ff::{FftField, PrimeField, UniformRand};
use ark_std::test_rng;
use ark_test_curves::bls12_381::{Fr, G1Projective};
use ark_test_curves::mnt4_753::Fq as MNT6Fr;

// Test multiplying various (low degree) polynomials together and
// comparing with naive evaluations.
#[test]
fn fft_composition() {
    fn test_fft_composition<
        F: FftField,
        R: rand::Rng,
        D: EvaluationDomain<F>,
    >(
        rng: &mut R,
        max_coeffs: usize,
    ) {
        for coeffs in 0..max_coeffs {
            let coeffs = 1 << coeffs;

            let domain = D::new(coeffs).unwrap();

            let mut v = vec![];
            for _ in 0..coeffs {
                v.push(F::rand(rng));
            }
            // Fill up with zeros.
            v.resize(domain.size(), F::zero());
            let mut v2 = v.clone();

            domain.ifft_in_place(&mut v2);
            domain.fft_in_place(&mut v2);
            assert_eq!(v, v2, "ifft(fft(.)) != iden");

            domain.fft_in_place(&mut v2);
            domain.ifft_in_place(&mut v2);
            assert_eq!(v, v2, "fft(ifft(.)) != iden");

            // domain.coset_ifft_in_place(&mut v2);
            // domain.coset_fft_in_place(&mut v2);
            // for i in 0..coeffs {
            //     if v[i] * v2[i] == F::multiplicative_generator().inverse().unwrap() {
            //         assert!(false, "ALERT coeff {:?} is wrong, num_coeffs {:?}", i, coeffs);
            //     }
            //     assert_eq!(v[i], v2[i], "coeff {:?} is wrong, num_coeffs {:?}", i, coeffs);
            // }
            // assert_eq!(v, v2, "coset_fft(coset_ifft(.)) != iden");

            domain.coset_fft_in_place(&mut v2);
            domain.coset_ifft_in_place(&mut v2);
            for i in 0..coeffs {
                if v[i] * v2[i] == F::multiplicative_generator().inverse().unwrap() {
                    assert!(false, "ALERT coeff {:?} is wrong, num_coeffs {:?}", i, coeffs);
                }
                assert_eq!(v[i], v2[i], "coeff {:?} is wrong, num_coeffs {:?}, {:?}, {:?}", i, coeffs, v[i].to_string(), v2[i].to_string());
            }
            assert_eq!(v, v2, "coset_ifft(coset_fft(.)) != iden");
        }
    }

    let rng = &mut test_rng();

    test_fft_composition::<Fr, _, GeneralEvaluationDomain<Fr>>(rng, 10);
    test_fft_composition::<Fr, _, GeneralEvaluationDomain<Fr>>(rng, 10);
    // This will result in a mixed-radix domain being used.
    // test_fft_composition::<MNT6Fr, _, MixedRadixEvaluationDomain<_>>(rng, 17);
}
