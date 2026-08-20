use ark_ec::{
    scalar_mul::{double_and_add, double_and_add_affine, glv::GLVConfig},
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup, PrimeGroup,
};
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
use ark_std::{ops::Mul, vec, UniformRand, Zero};

pub fn glv_scalar_decomposition<P: GLVConfig>() {
    let mut rng = ark_std::test_rng();
    for _i in 0..100 {
        let k = P::ScalarField::rand(&mut rng);

        let ((is_k1_positive, k1), (is_k2_positive, k2)) =
            <P as GLVConfig>::scalar_decomposition(k);

        if is_k1_positive && is_k2_positive {
            assert_eq!(k1 + k2 * P::LAMBDA, k);
        }
        if is_k1_positive && !is_k2_positive {
            assert_eq!(k1 - k2 * P::LAMBDA, k);
        }
        if !is_k1_positive && is_k2_positive {
            assert_eq!(-k1 + k2 * P::LAMBDA, k);
        }
        if !is_k1_positive && !is_k2_positive {
            assert_eq!(-k1 - k2 * P::LAMBDA, k);
        }

        // check if k1 and k2 are indeed small.
        let expected_max_bits = P::ScalarField::MODULUS_BIT_SIZE.div_ceil(2);
        assert!(
            k1.into_bigint().num_bits() <= expected_max_bits,
            "k1 has {} bits",
            k1.into_bigint().num_bits()
        );
        assert!(
            k2.into_bigint().num_bits() <= expected_max_bits,
            "k2 has {} bits",
            k2.into_bigint().num_bits()
        );
    }
}

pub fn glv_endomorphism_eigenvalue<P: GLVConfig>() {
    let g = Projective::generator();
    let endo_g = <P as GLVConfig>::endomorphism(&g);
    assert_eq!(endo_g, g.mul(P::LAMBDA));
}

pub fn glv_projective<P: GLVConfig>() {
    // check that glv_mul indeed computes the scalar multiplication
    let mut rng = ark_std::test_rng();

    let g = Projective::generator();
    for _i in 0..100 {
        let k = P::ScalarField::rand(&mut rng);

        let k_g = <P as GLVConfig>::glv_mul_projective(g, k);
        let k_g_2 = double_and_add(&g, k.into_bigint());
        assert_eq!(k_g, k_g_2);
    }
}

pub fn glv_affine<P: GLVConfig>() {
    // check that glv_mul indeed computes the scalar multiplication
    let mut rng = ark_std::test_rng();

    let g = Affine::generator();
    for _i in 0..100 {
        let k = P::ScalarField::rand(&mut rng);

        let k_g = <P as GLVConfig>::glv_mul_affine(g, k);
        let k_g_2 = double_and_add_affine(&g, k.into_bigint()).into_affine();
        assert_eq!(k_g, k_g_2);
    }
}

/// Structured inputs that random scalars are unlikely to reach: the identity base, a zero
/// scalar, and scalars whose half-scalars land on a wNAF window boundary.
pub fn glv_edge_cases<P: GLVConfig>() {
    let g = Projective::<P>::generator();

    // The identity absorbs every scalar, including ones that decompose to non-zero halves.
    let mut rng = ark_std::test_rng();
    for _ in 0..10 {
        let k = P::ScalarField::rand(&mut rng);
        assert!(<P as GLVConfig>::glv_mul_projective(Projective::<P>::zero(), k).is_zero());
        assert!(<P as GLVConfig>::glv_mul_affine(Affine::<P>::zero(), k).is_zero());
    }

    // `k = 0` decomposes to two zero half-scalars, so the scan produces no digits at all.
    assert!(<P as GLVConfig>::glv_mul_projective(g, P::ScalarField::ZERO).is_zero());

    let mut scalars = vec![
        P::ScalarField::ZERO,
        P::ScalarField::ONE,
        -P::ScalarField::ONE,
    ];

    // Around each of the first few powers of two. Recoding `2^n` and its neighbours exercises
    // the carry that makes a half-scalar one digit longer than its bit length, and the small
    // values force one half-scalar to zero while the other is non-zero.
    for n in 0..8u32 {
        let p = P::ScalarField::from(1u64 << n);
        scalars.extend([p - P::ScalarField::ONE, p, p + P::ScalarField::ONE]);
    }

    // All-ones runs, which recode to a single positive digit far above a long carry chain.
    for n in 1..=16u32 {
        scalars.push(P::ScalarField::from((1u64 << n) - 1));
    }

    // Scalars straddling the half-scalar boundary, where `k1` and `k2` differ most in length.
    let half = P::ScalarField::MODULUS_BIT_SIZE / 2;
    for shift in [half.saturating_sub(1), half, half + 1] {
        let p = P::ScalarField::from(2u64).pow([shift as u64]);
        scalars.extend([p - P::ScalarField::ONE, p, p + P::ScalarField::ONE]);
    }

    for k in scalars {
        assert_eq!(
            <P as GLVConfig>::glv_mul_projective(g, k),
            double_and_add(&g, k.into_bigint()),
            "glv_mul_projective disagrees at k = {k}",
        );
    }
}
