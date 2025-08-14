// The parameters for the curve have been taken from
// https://github.com/AztecProtocol/barretenberg/blob/97ccf76c42db581a8b8f8bfbcffe8ca015a3dd22/cpp/src/barretenberg/ecc/curves/grumpkin/grumpkin.hpp

use crate::{fq::Fq, fr::Fr};
use ark_ec::{
    models::CurveConfig,
    short_weierstrass::{self as sw, SWCurveConfig},
};
use ark_ff::{AdditiveGroup, Field, MontFp, Zero};

#[cfg(test)]
mod tests;

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct GrumpkinConfig;

impl CurveConfig for GrumpkinConfig {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x1];

    /// COFACTOR_INV = 1
    const COFACTOR_INV: Fr = Fr::ONE;
}

pub type Affine = sw::Affine<GrumpkinConfig>;
pub type Projective = sw::Projective<GrumpkinConfig>;

impl SWCurveConfig for GrumpkinConfig {
    /// COEFF_A = 0
    const COEFF_A: Fq = Fq::ZERO;

    /// COEFF_B = -17
    const COEFF_B: Fq = MontFp!("-17");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const GENERATOR: Affine = Affine::new_unchecked(G_GENERATOR_X, G_GENERATOR_Y);

    /// Correctness:
    /// Substituting (0, 0) into the curve equation gives 0^2 = b.
    /// Since b is not zero, the point (0, 0) is not on the curve.
    /// Therefore, we can safely use (0, 0) as a flag for the zero point.
    type ZeroFlag = ();

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

/// G_GENERATOR_X = 1
pub const G_GENERATOR_X: Fq = MontFp!("1");

/// G_GENERATOR_Y = sqrt(-16)
pub const G_GENERATOR_Y: Fq =
    MontFp!("17631683881184975370165255887551781615748388533673675138860");
