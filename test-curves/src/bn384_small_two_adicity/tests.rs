#![allow(unused_imports)]
use ark_ec::{models::SWModelParameters, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{One, UniformRand, Zero};
use ark_std::rand::Rng;

use crate::bn384_small_two_adicity::{g1, Fq, FqParameters, Fr, G1Affine, G1Projective};
use ark_algebra_test_templates::{
    curves::*, fields::*, generate_base_field_test, generate_g1_test, groups::*, msm::*,
};

pub(crate) const ITERATIONS: usize = 5;

generate_base_field_test!(bn384_small_two_adicity);
generate_g1_test!(bn384_small_two_adicity);
