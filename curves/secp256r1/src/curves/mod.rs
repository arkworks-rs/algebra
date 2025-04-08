use ark_ec::{
    models::CurveConfig,
    short_weierstrass::{self as sw, SWCurveConfig},
};
use ark_ff::{Field, MontFp};

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
    const COFACTOR_INV: Fr = Fr::ONE;
}

impl SWCurveConfig for Config {
    /// COEFF_A = -3
    const COEFF_A: Fq = MontFp!("-3");

    /// COEFF_B = 41058363725152142129326129780047268409114441015993725554835256314039467401291
    const COEFF_B: Fq =
        MontFp!("41058363725152142129326129780047268409114441015993725554835256314039467401291");

    /// GENERATOR = (G_GENERATOR_X, G_GENERATOR_Y)
    const GENERATOR: Affine = Affine::new_unchecked(G_GENERATOR_X, G_GENERATOR_Y);
}

/// G_GENERATOR_X =
/// 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
pub const G_GENERATOR_X: Fq =
    MontFp!("48439561293906451759052585252797914202762949526041747995844080717082404635286");

/// G_GENERATOR_Y =
/// 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
pub const G_GENERATOR_Y: Fq =
    MontFp!("36134250956749795798585127919587881956611106672985015071877198253568414405109");
