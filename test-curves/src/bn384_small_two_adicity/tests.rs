#![allow(unused_imports)]
use ark_ec::{models::SWModelParameters, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, One, SquareRootField, UniformRand, Zero};
use ark_std::{rand::Rng, test_rng};

use crate::bn384_small_two_adicity::{g1, Fq, FqConfig, Fr, FrConfig, G1Affine, G1Projective};
use ark_algebra_test_templates::{
    curves::*, fields::*, generate_field_test, generate_g1_test, groups::*, msm::*,
};

use ark_std::ops::{AddAssign, MulAssign, SubAssign};

generate_field_test!(bn384_small_two_adicity; mont(6, 6););
generate_g1_test!(bn384_small_two_adicity; curve_tests; sw_tests;);
