use ark_ec::{
    models::CurveConfig,
    short_weierstrass::{self as sw, SWCurveConfig},
};
use ark_ff::{AdditiveGroup, Field, MontFp, Zero};

use crate::{fq::Fq, fr::Fr};

#[cfg(test)]
mod tests;

pub type Affine = sw::Affine<Config>;
pub type Projective = sw::Projective<Config>;

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x1];

    /// COFACTOR_INV = COFACTOR^{-1} mod r = 1
    #[rustfmt::skip]
    const COFACTOR_INV: Fr =  Fr::ONE;
}

impl SWCurveConfig for Config {
    /// COEFF_A = 0
    const COEFF_A: Fq = Fq::ZERO;

    /// COEFF_B = 7
    const COEFF_B: Fq = MontFp!("7");

    /// GENERATOR = (G_GENERATOR_X, G_GENERATOR_Y)
    const GENERATOR: Affine = Affine::new_unchecked(G_GENERATOR_X, G_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

/// G_GENERATOR_X =
/// 55066263022277343669578718895168534326250603453777594175500187360389116729240
pub const G_GENERATOR_X: Fq =
    MontFp!("55066263022277343669578718895168534326250603453777594175500187360389116729240");

/// G_GENERATOR_Y =
/// 32670510020758816978083085130507043184471273380659243275938904335757337482424
pub const G_GENERATOR_Y: Fq =
    MontFp!("32670510020758816978083085130507043184471273380659243275938904335757337482424");
