use crate::{Fq, Fr};
use ark_ec::{
    models::CurveConfig,
    twisted_edwards::{Affine, MontCurveConfig, MontgomeryAffine, Projective, TECurveConfig},
};
use ark_ff::MontFp;

#[cfg(test)]
mod tests;

pub type EdwardsAffine = Affine<Curve25519Config>;
pub type EdwardsProjective = Projective<Curve25519Config>;
pub type NonZeroMontgomeryAffine = MontgomeryAffine<Curve25519Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Curve25519Config;

impl CurveConfig for Curve25519Config {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 8
    const COFACTOR: &'static [u64] = &[8];

    /// COFACTOR_INV (mod r) =
    /// 2713877091499598330239944961141122840321418634767465352250731601857045344121
    const COFACTOR_INV: Fr =
        MontFp!("2713877091499598330239944961141122840321418634767465352250731601857045344121");
}

// We want to emphasize that this twisted Edwards curve is not ed25519.
// Ed25519 has COEFF_A = -1 and COEFF_D = -121665 / 121666.
impl TECurveConfig for Curve25519Config {
    /// COEFF_A = 486664
    const COEFF_A: Fq = MontFp!("486664");

    /// COEFF_D = 486660
    const COEFF_D: Fq = MontFp!("486660");

    /// Standard generators from <https://neuromancer.sk/std/other/Curve25519>.
    /// The Montgomery form is
    ///     x = 0x09,
    ///     y = 0x20ae19a1b8a086b4e01edd2c7748d14c923d4d7e6d7c61b229e9c5a27eced3d9
    /// The twisted Edwards form is
    ///     x = 0x547c4350219f5e19dd26a3d6668b74346a8eb726eb2396e1228cfa397ffe6bd4
    ///     y = 0x6666666666666666666666666666666666666666666666666666666666666658
    const GENERATOR: EdwardsAffine = EdwardsAffine::new_unchecked(GENERATOR_X, GENERATOR_Y);

    type MontCurveConfig = Curve25519Config;
}

impl MontCurveConfig for Curve25519Config {
    /// COEFF_A = 486662
    const COEFF_A: Fq = MontFp!("486662");

    /// COEFF_B = 1
    const COEFF_B: Fq = MontFp!("1");

    type TECurveConfig = Curve25519Config;
}

/// GENERATOR_X =
/// 38213832894368730265794714087330135568483813637251082400757400312561599933396
pub const GENERATOR_X: Fq =
    MontFp!("38213832894368730265794714087330135568483813637251082400757400312561599933396");

/// GENERATOR_Y =
/// (4/5)
/// 46316835694926478169428394003475163141307993866256225615783033603165251855960
pub const GENERATOR_Y: Fq =
    MontFp!("46316835694926478169428394003475163141307993866256225615783033603165251855960");
