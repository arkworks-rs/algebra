use std::ops::Mul;

use ark_ec::{
    scalar_mul::{glv::GLVConfig, sw_double_and_add_affine, sw_double_and_add_projective},
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup, PrimeGroup,
};
use ark_ff::PrimeField;
use ark_std::UniformRand;

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
        // could be nice to check if k1 and k2 are indeed small.
    }
}

pub fn glv_endomorphism_eigenvalue<P: GLVConfig>() {
    let g = Projective::<P>::generator();
    let endo_g = <P as GLVConfig>::endomorphism(&g);
    assert_eq!(endo_g, g.mul(P::LAMBDA));
}

pub fn glv_projective<P: GLVConfig>() {
    // check that glv_mul indeed computes the scalar multiplication
    let mut rng = ark_std::test_rng();

    let g = Projective::<P>::generator();
    for _i in 0..100 {
        let k = P::ScalarField::rand(&mut rng);

        let k_g = <P as GLVConfig>::glv_mul_projective(g, k);
        let k_g_2 = sw_double_and_add_projective(&g, &k.into_bigint());
        assert_eq!(k_g, k_g_2);
    }
}

pub fn glv_affine<P: GLVConfig>() {
    // check that glv_mul indeed computes the scalar multiplication
    let mut rng = ark_std::test_rng();

    let g = Affine::<P>::generator();
    for _i in 0..100 {
        let k = P::ScalarField::rand(&mut rng);

        let k_g = <P as GLVConfig>::glv_mul_affine(g, k);
        let k_g_2 = sw_double_and_add_affine(&g, &k.into_bigint()).into_affine();
        assert_eq!(k_g, k_g_2);
    }
}
