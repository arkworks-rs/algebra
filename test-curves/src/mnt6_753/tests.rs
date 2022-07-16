#![allow(unused_imports)]
use ark_ec::{
    models::short_weierstrass::SWCurveConfig, AffineCurve, PairingEngine, ProjectiveCurve,
};
use ark_ff::{Field, One, UniformRand, Zero};

use crate::mnt6_753::{Fq, Fq3, FqConfig, Fr, FrConfig};
use ark_algebra_test_templates::{
    curves::*, fields::*, generate_field_test, generate_g1_test, msm::*,
};
use ark_std::{
    ops::{AddAssign, MulAssign, SubAssign},
    rand::Rng,
    test_rng,
};

generate_field_test!(mnt6_753; fq3; );
