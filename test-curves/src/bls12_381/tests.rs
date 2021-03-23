#![allow(unused_imports)]
use ark_ec::{models::SWModelParameters, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{One, UniformRand, Zero};

use crate::bls12_381::{g1, Fq, FqParameters, Fr, G1Affine, G1Projective};
use ark_algebra_test_templates::{curves::*, fields::*, groups::*, msm::test_var_base_msm};
use ark_std::rand::Rng;

pub(crate) const ITERATIONS: usize = 5;

#[test]
fn test_fr() {
    let mut rng = ark_std::test_rng();
    for _ in 0..ITERATIONS {
        let a: Fr = UniformRand::rand(&mut rng);
        let b: Fr = UniformRand::rand(&mut rng);
        field_test(a, b);
        primefield_test::<Fr>();
        sqrt_field_test(b);
    }
}

#[test]
fn test_fq() {
    let mut rng = ark_std::test_rng();
    for _ in 0..ITERATIONS {
        let a: Fq = UniformRand::rand(&mut rng);
        let b: Fq = UniformRand::rand(&mut rng);
        field_test(a, b);
        primefield_test::<Fq>();
        sqrt_field_test(a);
    }
}

#[test]
fn test_g1_generator() {
    let generator = G1Affine::prime_subgroup_generator();
    assert!(generator.is_on_curve());
    assert!(generator.is_in_correct_subgroup_assuming_on_curve());
}

#[test]
fn test_g1() {
    curve_tests::<G1Projective>();
    sw_tests::<g1::Parameters>();
    group_tests::<G1Projective>();
    test_var_base_msm::<G1Affine>();
}
