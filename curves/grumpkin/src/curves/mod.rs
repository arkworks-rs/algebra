// The parameters for the curve have been taken from
// https://github.com/AztecProtocol/barretenberg/blob/97ccf76c42db581a8b8f8bfbcffe8ca015a3dd22/cpp/src/barretenberg/ecc/curves/grumpkin/grumpkin.hpp

use crate::{fq::Fq, fr::Fr};
use ark_ec::scalar_mul::glv::GLVConfig;
use ark_ec::{
    models::CurveConfig,
    short_weierstrass::{self as sw, SWCurveConfig},
};
use ark_ff::{AdditiveGroup, BigInt, Field, MontFp, PrimeField, Zero};

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

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

impl GLVConfig for GrumpkinConfig {
    const ENDO_COEFFS: &'static [Self::BaseField] = &[MontFp!(
        "21888242871839275217838484774961031246154997185409878258781734729429964517155"
    )];
    const LAMBDA: Self::ScalarField =
        (MontFp!("21888242871839275220042445260109153167277707414472061641714758635765020556616"));
    const SCALAR_DECOMP_COEFFS: [(bool, <Self::ScalarField as PrimeField>::BigInt); 4] = [
        (false, BigInt!("9931322734385697762")),
        (false, BigInt!("147946756881789319010696353538189108491")),
        (false, BigInt!("147946756881789319000765030803803410729")),
        (true, BigInt!("9931322734385697762")),
    ];

    fn endomorphism(p: &Projective) -> Projective {
        let mut res = (*p).clone();
        res.x *= Self::ENDO_COEFFS[0];
        res
    }

    fn endomorphism_affine(p: &Affine) -> Affine {
        let mut res = (*p).clone();
        res.x *= Self::ENDO_COEFFS[0];
        res
    }
}

/// G_GENERATOR_X = 1
pub const G_GENERATOR_X: Fq = MontFp!("1");

/// G_GENERATOR_Y = sqrt(-16)
pub const G_GENERATOR_Y: Fq =
    MontFp!("17631683881184975370165255887551781615748388533673675138860");
