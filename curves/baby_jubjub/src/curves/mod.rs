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
/// Baby-JubJub's curve equation: Ax^2 + y^2 = 1 + Dx^2y^2, where
///    * A = 168700
///    * D = 168696
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
    /// COEFF_A = 168700
    const COEFF_A: Fq = MontFp!("168700");

    /// COEFF_D = 168696
    const COEFF_D: Fq = MontFp!("168696");

    /// Standard base points from https://eips.ethereum.org/EIPS/eip-2494.
    /// Note: A base point B is used instead of a generator G satisfying B = 8 * G.
    /// The Montgomery form is
    ///     x = 7,
    ///     y = 4258727773875940690362607550498304598101071202821725296872974770776423442226
    /// The twisted Edwards form is
    ///     x = 995203441582195749578291179787384436505546430278305826713579947235728471134
    ///     y = 5472060717959818805561601436314318772137091100104008585924551046643952123905
    const GENERATOR: EdwardsAffine = EdwardsAffine::new_unchecked(GENERATOR_X, GENERATOR_Y);

    type MontCurveConfig = EdwardsConfig;
}

impl MontCurveConfig for EdwardsConfig {
    /// COEFF_A = 168698
    const COEFF_A: Fq = MontFp!("168698");
    /// COEFF_B = 1
    const COEFF_B: Fq = Fq::ONE;

    type TECurveConfig = EdwardsConfig;
}

/// GENERATOR_X =
/// 5299619240641551281634865583518297030282874472190772894086521144482721001553
pub const GENERATOR_X: Fq =
    MontFp!("5299619240641551281634865583518297030282874472190772894086521144482721001553");

/// GENERATOR_Y =
/// 16950150798460657717958625567821834550301663161624707787222815936182638968203
pub const GENERATOR_Y: Fq =
    MontFp!("16950150798460657717958625567821834550301663161624707787222815936182638968203");
