use ark_ec::{
    mnt4,
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
};
use ark_ff::{Field, MontFp};

use crate::{Fq, Fr};

pub type G1Affine = mnt4::G1Affine<crate::Config>;
pub type G1Projective = mnt4::G1Projective<crate::Config>;
pub type G1Prepared = mnt4::G1Prepared<crate::Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[1];

    /// COFACTOR^(-1) mod r =
    /// 1
    const COFACTOR_INV: Fr = Fr::ONE;
}

impl SWCurveConfig for Config {
    /// COEFF_A = 2
    /// Reference: <https://github.com/scipr-lab/libff/blob/c927821ebe02e0a24b5e0f9170cec5e211a35f08/libff/algebra/curves/mnt/mnt4/mnt4_init.cpp#L116>
    const COEFF_A: Fq = MontFp!("2");

    /// COEFF_B = 423894536526684178289416011533888240029318103673896002803341544124054745019340795360841685
    /// Reference: <https://github.com/scipr-lab/libff/blob/c927821ebe02e0a24b5e0f9170cec5e211a35f08/libff/algebra/curves/mnt/mnt4/mnt4_init.cpp#L117>
    const COEFF_B: Fq = MontFp!("423894536526684178289416011533888240029318103673896002803341544124054745019340795360841685");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const GENERATOR: G1Affine = G1Affine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);

    /// Correctness:
    /// Substituting (0, 0) into the curve equation gives 0^2 = b.
    /// Since b is not zero, the point (0, 0) is not on the curve.
    /// Therefore, we can safely use (0, 0) as a flag for the zero point.
    type ZeroFlag = bool;
}

// Generator of G1
// X = 60760244141852568949126569781626075788424196370144486719385562369396875346601926534016838,
// Y = 363732850702582978263902770815145784459747722357071843971107674179038674942891694705904306,
/// G1_GENERATOR_X
/// Reference: <https://github.com/scipr-lab/libff/blob/c927821ebe02e0a24b5e0f9170cec5e211a35f08/libff/algebra/curves/mnt/mnt4/mnt4_init.cpp#L137>
pub const G1_GENERATOR_X: Fq = MontFp!(
    "60760244141852568949126569781626075788424196370144486719385562369396875346601926534016838"
);

/// G1_GENERATOR_Y
/// Reference: <https://github.com/scipr-lab/libff/blob/c927821ebe02e0a24b5e0f9170cec5e211a35f08/libff/algebra/curves/mnt/mnt4/mnt4_init.cpp#L138>
pub const G1_GENERATOR_Y: Fq = MontFp!(
    "363732850702582978263902770815145784459747722357071843971107674179038674942891694705904306"
);
