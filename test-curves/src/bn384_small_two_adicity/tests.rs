#![allow(unused_imports)]
use ark_ec::{
    models::short_weierstrass::SWCurveConfig, pairing::Pairing, AffineRepr, CurveGroup, PrimeGroup,
};
use ark_ff::{Field, One, UniformRand, Zero};
use ark_std::{rand::Rng, test_rng};

use crate::bn384_small_two_adicity::{Fq, FqConfig, Fr, FrConfig, G1Affine, G1Projective};
use ark_algebra_test_templates::*;
use ark_std::ops::{AddAssign, MulAssign, SubAssign};

test_field!(fr; Fr; mont_prime_field);
test_field!(fq; Fq; mont_prime_field);
test_group!(g1; G1Projective; sw);
