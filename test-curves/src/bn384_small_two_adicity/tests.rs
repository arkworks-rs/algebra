#![allow(unused_imports)]
use ark_ec::{
    models::short_weierstrass::SWCurveConfig, pairing::Pairing, AffineRepr, CurveGroup, PrimeGroup,
};
use ark_ff::{Field, One, UniformRand, Zero};
use ark_std::{rand::Rng, test_rng};

#[cfg(feature = "bn384_small_two_adicity_base_field")]
use crate::bn384_small_two_adicity::{Fq, FqConfig};
#[cfg(feature = "bn384_small_two_adicity_scalar_field")]
use crate::bn384_small_two_adicity::{Fr, FrConfig};
#[cfg(feature = "bn384_small_two_adicity_curve")]
use crate::bn384_small_two_adicity::{G1Affine, G1Projective};
use ark_algebra_test_templates::*;
#[cfg(feature = "bn384_small_two_adicity_curve")]
use ark_ec_test_templates::*;
use ark_std::ops::{AddAssign, MulAssign, SubAssign};

#[cfg(feature = "bn384_small_two_adicity_scalar_field")]
test_field!(fr; Fr; mont_prime_field);
#[cfg(feature = "bn384_small_two_adicity_base_field")]
test_field!(fq; Fq; mont_prime_field);
#[cfg(feature = "bn384_small_two_adicity_curve")]
test_group!(g1; G1Projective; sw);
