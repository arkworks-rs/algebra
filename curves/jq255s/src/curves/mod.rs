use ark_ec::{
    double_odd::{self as doo, DOCurveConfig},
    models::CurveConfig,
};
use ark_ff::MontFp;

use crate::{fq::Fq, fr::Fr};

#[cfg(test)]
mod tests;

pub type Affine = doo::Affine<Config>;
pub type Projective = doo::Projective<Config>;

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 2
    const COFACTOR: &'static [u64] = &[2];

    #[rustfmt::skip]
    const COFACTOR_INV: Fr = MontFp!("14474011154664524427946373126085988481687200150840406918337755177497658435940");
}

impl DOCurveConfig for Config {
    /// COEFF_A = -1
    const COEFF_A: Fq = MontFp!("-1");

    /// COEFF_B = 1/2
    const COEFF_B: Fq =
        MontFp!("28948022309329048855892746252171976963317496166410141009864396001978282408006");

    /// GENERATOR = (G_GENERATOR_X, G_GENERATOR_Y)
    const GENERATOR: Affine = Affine::new_unchecked(G_GENERATOR_E, G_GENERATOR_U);
}

/// G_GENERATOR_X =
/// 0x0076aab95b2acbae4747482ba7081f7b94193dad9f96fdd2516283980459b09eaa
pub const G_GENERATOR_E: Fq =
    MontFp!("6929650852805837546485348833751579670837850621479164143703164723313568683024");

/// G_GENERATOR_Y =
/// 0x00b7d601b4cb25f8249b65e89b8f584a5494e592f3895d54f9002202b0530e6fbc
pub const G_GENERATOR_U: Fq = MontFp!("3");
