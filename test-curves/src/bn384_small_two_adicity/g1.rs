use ark_ec::{
    models::CurveConfig,
    short_weierstrass::{self, *},
};
use ark_ff::Zero;

use crate::bn384_small_two_adicity::{Fq, Fr, FR_ONE};

pub type G1Affine = Affine<Config>;
pub type G1Projective = Projective<Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[1];

    /// COFACTOR_INV = COFACTOR^{-1} mod r = 1
    const COFACTOR_INV: Fr = FR_ONE;
}

impl short_weierstrass::SWCurveConfig for Config {
    /// COEFF_A = 0
    const COEFF_A: Fq = ark_ff::MontFp!("0");

    /// COEFF_B = 17
    const COEFF_B: Fq = ark_ff::MontFp!("17");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const GENERATOR: G1Affine = G1Affine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

/// G1_GENERATOR_X = -1
pub const G1_GENERATOR_X: Fq = ark_ff::MontFp!("-1");

/// G1_GENERATOR_Y = 4
pub const G1_GENERATOR_Y: Fq = ark_ff::MontFp!("4");
