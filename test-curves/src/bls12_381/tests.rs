#![allow(unused_imports)]
use ark_ec::{models::SWModelParameters, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, One, UniformRand, Zero};

use crate::bls12_381::{g1, Fq, Fq2, Fq6, FqParameters, Fr, G1Affine, G1Projective};
use ark_algebra_test_templates::{
    curves::*, fields::*, generate_base_field_test, generate_base_fq2_test, generate_base_fq6_test,
    generate_g1_test, groups::*, msm::*,
};
use ark_std::rand::Rng;

pub(crate) const ITERATIONS: usize = 5;

generate_base_field_test!(bls12_381);
generate_base_fq2_test!(bls12_381);
generate_base_fq6_test!(bls12_381);
generate_g1_test!(bls12_381);
