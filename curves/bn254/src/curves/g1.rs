use ark_ec::{
    bn,
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
    scalar_mul::glv::GLVConfig,
    short_weierstrass::{Affine, Projective},
};
use ark_ff::{AdditiveGroup, BigInt, Field, MontFp, PrimeField, Zero};

use crate::{Fq, Fr};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

pub type G1Affine = Affine<Config>;

impl CurveConfig for Config {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x1];

    /// COFACTOR_INV = COFACTOR^{-1} mod r = 1
    const COFACTOR_INV: Fr = Fr::ONE;
}

impl SWCurveConfig for Config {
    /// COEFF_A = 0
    const COEFF_A: Fq = Fq::ZERO;

    /// COEFF_B = 3
    const COEFF_B: Fq = MontFp!("3");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const GENERATOR: G1Affine = G1Affine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }

    #[inline]
    fn mul_projective(
        p: &bn::G1Projective<crate::Config>,
        scalar: &[u64],
    ) -> bn::G1Projective<crate::Config> {
        let s = Self::ScalarField::from_sign_and_limbs(true, scalar);
        GLVConfig::glv_mul_projective(*p, s)
    }

    #[inline]
    fn is_in_correct_subgroup_assuming_on_curve(_p: &G1Affine) -> bool {
        // G1 = E(Fq) so if the point is on the curve, it is also in the subgroup.
        true
    }
}

impl GLVConfig for Config {
    const ENDO_COEFFS: &'static [Self::BaseField] = &[MontFp!(
        "21888242871839275220042445260109153167277707414472061641714758635765020556616"
    )];

    const LAMBDA: Self::ScalarField =
        MontFp!("21888242871839275217838484774961031246154997185409878258781734729429964517155");

    const SCALAR_DECOMP_COEFFS: [(bool, <Self::ScalarField as PrimeField>::BigInt); 4] = [
        (false, BigInt!("147946756881789319000765030803803410728")),
        (true, BigInt!("9931322734385697763")),
        (false, BigInt!("9931322734385697763")),
        (false, BigInt!("147946756881789319010696353538189108491")),
    ];

    fn endomorphism(p: &Projective<Self>) -> Projective<Self> {
        let mut res = (*p).clone();
        res.x *= Self::ENDO_COEFFS[0];
        res
    }
    fn endomorphism_affine(p: &Affine<Self>) -> Affine<Self> {
        let mut res = (*p).clone();
        res.x *= Self::ENDO_COEFFS[0];
        res
    }
}

/// G1_GENERATOR_X = 1
pub const G1_GENERATOR_X: Fq = Fq::ONE;

/// G1_GENERATOR_Y = 2
pub const G1_GENERATOR_Y: Fq = MontFp!("2");
