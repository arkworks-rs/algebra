use ark_ec::{
    mnt6,
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
};
use ark_ff::{Field, MontFp};

use crate::{Fq, Fr};

pub type G1Affine = mnt6::G1Affine<crate::Config>;
pub type G1Projective = mnt6::G1Projective<crate::Config>;
pub type G1Prepared = mnt6::G1Prepared<crate::Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[1];

    /// COFACTOR^(-1) mod r = 1
    const COFACTOR_INV: Fr = Fr::ONE;
}

impl SWCurveConfig for Config {
    /// COEFF_A = 11
    const COEFF_A: Fq = MontFp!("11");

    /// COEFF_B = 106700080510851735677967319632585352256454251201367587890185989362936000262606668469523074
    const COEFF_B: Fq = MontFp!("106700080510851735677967319632585352256454251201367587890185989362936000262606668469523074");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const GENERATOR: G1Affine = G1Affine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);
}

/// G1_GENERATOR_X =
pub const G1_GENERATOR_X: Fq = MontFp!(
    "336685752883082228109289846353937104185698209371404178342968838739115829740084426881123453"
);

/// G1_GENERATOR_Y =

pub const G1_GENERATOR_Y: Fq = MontFp!(
    "402596290139780989709332707716568920777622032073762749862342374583908837063963736098549800"
);
