use crate::{Fq, Fr};
use ark_ec::{
    models::CurveConfig,
    twisted_edwards::{Affine, MontCurveConfig, Projective, TECurveConfig},
};
use ark_ff::MontFp;

#[cfg(test)]
mod tests;

pub type EdwardsAffine = Affine<EdwardsConfig>;
pub type EdwardsProjective = Projective<EdwardsConfig>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct EdwardsConfig;

impl CurveConfig for EdwardsConfig {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 8
    const COFACTOR: &'static [u64] = &[8];

    /// COFACTOR_INV (mod r) =
    /// 2713877091499598330239944961141122840321418634767465352250731601857045344121
    const COFACTOR_INV: Fr =
        MontFp!("2713877091499598330239944961141122840321418634767465352250731601857045344121");
}

impl TECurveConfig for EdwardsConfig {
    /// COEFF_A = -1
    const COEFF_A: Fq = MontFp!("-1");

    /// COEFF_D = -121665 / 121666
    const COEFF_D: Fq =
        MontFp!("37095705934669439343138083508754565189542113879843219016388785533085940283555");

    /// Standard generators from <https://neuromancer.sk/std/other/Ed25519>.
    const GENERATOR: EdwardsAffine = EdwardsAffine::new_unchecked(GENERATOR_X, GENERATOR_Y);

    type MontCurveConfig = EdwardsConfig;

    /// Multiplication by `a` is just negation.
    #[inline(always)]
    fn mul_by_a(elem: Self::BaseField) -> Self::BaseField {
        -elem
    }
}

// We want to emphasize that this Montgomery curve is not Curve25519.
impl MontCurveConfig for EdwardsConfig {
    /// COEFF_A = 486662
    const COEFF_A: Fq = MontFp!("486662");

    /// COEFF_B = 57896044618658097711785492504343953926634992332820282019728792003956564333285
    /// This is not one, because ed25519 != curve25519
    const COEFF_B: Fq =
        MontFp!("57896044618658097711785492504343953926634992332820282019728792003956564333285");

    type TECurveConfig = EdwardsConfig;
}

/// GENERATOR_X =
/// 15112221349535400772501151409588531511454012693041857206046113283949847762202
pub const GENERATOR_X: Fq =
    MontFp!("15112221349535400772501151409588531511454012693041857206046113283949847762202");

/// GENERATOR_Y =
/// (4/5)
/// 46316835694926478169428394003475163141307993866256225615783033603165251855960
pub const GENERATOR_Y: Fq =
    MontFp!("46316835694926478169428394003475163141307993866256225615783033603165251855960");
