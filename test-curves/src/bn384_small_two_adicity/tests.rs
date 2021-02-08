#![allow(unused_imports)]
use ark_ec::{models::SWModelParameters, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{One, UniformRand, Zero};
use ark_std::rand::Rng;

use crate::bn384_small_two_adicity::{g1, Fq, FqParameters, Fr, G1Affine, G1Projective};
use ark_algebra_test_templates::{curves::*, fields::*, groups::*};

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
fn test_g1_projective_curve() {
    curve_tests::<G1Projective>();
    sw_tests::<g1::Parameters>();
}

#[test]
fn test_g1_projective_group() {
    let mut rng = ark_std::test_rng();
    let a: G1Projective = rng.gen();
    let b: G1Projective = rng.gen();
    group_test(a, b);
}

#[test]
fn test_g1_generator() {
    let generator = G1Affine::prime_subgroup_generator();
    assert!(generator.is_on_curve());
    assert!(generator.is_in_correct_subgroup_assuming_on_curve());
}
