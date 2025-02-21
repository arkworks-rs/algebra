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
    #[rustfmt::skip]
    const COFACTOR_INV: Fr =  Fr::ONE;
}

impl SWCurveConfig for Config {
    /// COEFF_A = 115792089210356248762697446949407573530594504085698471288169790229257723883796
    const COEFF_A: Fq =
        MontFp!("115792089210356248762697446949407573530594504085698471288169790229257723883796");

    /// COEFF_B = 81531206846337786915455327229510804132577517753388365729879493166393691077718
    const COEFF_B: Fq =
        MontFp!("81531206846337786915455327229510804132577517753388365729879493166393691077718");

    /// GENERATOR = (G_GENERATOR_X, G_GENERATOR_Y)
    const GENERATOR: Affine = Affine::new_unchecked(G_GENERATOR_X, G_GENERATOR_Y);
}

/// G_GENERATOR_X =
/// 3
pub const G_GENERATOR_X: Fq = MontFp!("3");

/// G_GENERATOR_Y =
/// 40902200210088653215032584946694356296222563095503428277299570638400093548589
pub const G_GENERATOR_Y: Fq =
    MontFp!("40902200210088653215032584946694356296222563095503428277299570638400093548589");
