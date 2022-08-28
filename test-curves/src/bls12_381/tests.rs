#![allow(unused_imports)]
use ark_ec::{
    models::short_weierstrass::SWCurveConfig, AffineCurve, PairingEngine, ProjectiveCurve,
};
use ark_ff::{Field, One, UniformRand, Zero};

use crate::bls12_381::{Fq, FqConfig, Fr, FrConfig};

#[cfg(feature = "bls12_381_curve")]
use crate::bls12_381::{g1, Fq2, Fq6, G1Affine, G1Projective};
#[cfg(feature = "bls12_381_curve")]
use ark_ec::bls12::{Bls12, Bls12Parameters, TwistType};

use ark_algebra_test_templates::{curves::*, fields::*, generate_field_test, msm::*};

#[cfg(feature = "bls12_381_curve")]
use ark_algebra_test_templates::{curves::*, generate_g1_test, msm::*};

use ark_std::{
    ops::{AddAssign, MulAssign, SubAssign},
    rand::Rng,
    test_rng,
};

#[cfg(feature = "bls12_381_curve")]
generate_field_test!(bls12_381; fq2; fq6; mont(6, 4); );

#[cfg(not(feature = "bls12_381_curve"))]
generate_field_test!(bls12_381; mont(6, 4); );

#[cfg(feature = "bls12_381_curve")]
generate_g1_test!(bls12_381; curve_tests; sw_tests;);
