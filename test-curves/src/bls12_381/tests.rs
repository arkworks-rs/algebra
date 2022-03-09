#![allow(unused_imports)]
use ark_ec::{models::SWModelParameters, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, One, SquareRootField, UniformRand, Zero};

use crate::bls12_381::{g1, Fq, Fq2, Fq6, FqConfig, Fr, FrConfig, G1Affine, G1Projective};
use ark_algebra_test_templates::{
    curves::*, fields::*, generate_field_test, generate_g1_test, groups::*, msm::*,
};
use ark_std::{
    ops::{AddAssign, MulAssign, SubAssign},
    rand::Rng,
    test_rng,
};

generate_field_test!(bls12_381; fq2; fq6; mont(6, 4); );
generate_g1_test!(bls12_381; curve_tests; sw_tests;);
