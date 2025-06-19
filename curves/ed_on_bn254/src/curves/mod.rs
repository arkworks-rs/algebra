use ark_ec::{
    models::CurveConfig,
    twisted_edwards::{Affine, MontCurveConfig, Projective, TECurveConfig},
};
use ark_ff::{Field, MontFp};

use crate::{Fq, Fr};

#[cfg(test)]
mod tests;

pub type EdwardsAffine = Affine<EdwardsConfig>;
pub type EdwardsProjective = Projective<EdwardsConfig>;

/// `Baby-JubJub` is a twisted Edwards curve. These curves have equations of the
/// form: ax² + y² = 1 + dx²y².
/// over some base finite field Fq.
///
/// Baby-JubJub's curve equation: x² + y² = 1 + (168696/168700)x²y²
///
/// q = 21888242871839275222246405745257275088548364400416034343698204186575808495617
#[derive(Clone, Default, PartialEq, Eq)]
pub struct EdwardsConfig;

impl CurveConfig for EdwardsConfig {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 8
    const COFACTOR: &'static [u64] = &[8];

    /// COFACTOR^(-1) mod r =
    /// 2394026564107420727433200628387514462817212225638746351800188703329891451411
    const COFACTOR_INV: Fr =
        MontFp!("2394026564107420727433200628387514462817212225638746351800188703329891451411");
}

impl TECurveConfig for EdwardsConfig {
    /// COEFF_A = 1
    const COEFF_A: Fq = Fq::ONE;

    #[inline(always)]
    fn mul_by_a(elem: Self::BaseField) -> Self::BaseField {
        elem
    }

    /// COEFF_D = 168696/168700 mod q
    ///         = 9706598848417545097372247223557719406784115219466060233080913168975159366771
    const COEFF_D: Fq =
        MontFp!("9706598848417545097372247223557719406784115219466060233080913168975159366771");

    /// AFFINE_GENERATOR_COEFFS = (GENERATOR_X, GENERATOR_Y)
    const GENERATOR: EdwardsAffine = EdwardsAffine::new_unchecked(GENERATOR_X, GENERATOR_Y);

    type MontCurveConfig = EdwardsConfig;
}

impl MontCurveConfig for EdwardsConfig {
    /// COEFF_A = 168698
    const COEFF_A: Fq = MontFp!("168698");
    /// COEFF_B = 168700
    const COEFF_B: Fq = MontFp!("168700");

    type TECurveConfig = EdwardsConfig;
}

/// GENERATOR_X =
/// 19698561148652590122159747500897617769866003486955115824547446575314762165298
pub const GENERATOR_X: Fq =
    MontFp!("19698561148652590122159747500897617769866003486955115824547446575314762165298");

/// GENERATOR_Y =
/// 19298250018296453272277890825869354524455968081175474282777126169995084727839
pub const GENERATOR_Y: Fq =
    MontFp!("19298250018296453272277890825869354524455968081175474282777126169995084727839");
