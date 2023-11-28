use ark_ec::{
    models::CurveConfig,
    scalar_mul::glv::GLVConfig,
    short_weierstrass::{self as sw, SWCurveConfig},
};
use ark_ff::{AdditiveGroup, BigInt, Field, MontFp, PrimeField, Zero};

use crate::{fq::Fq, fr::Fr};

#[cfg(test)]
mod tests;

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct PallasConfig;

impl CurveConfig for PallasConfig {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x1];

    /// COFACTOR_INV = 1
    const COFACTOR_INV: Fr = Fr::ONE;
}

pub type Affine = sw::Affine<PallasConfig>;
pub type Projective = sw::Projective<PallasConfig>;

impl SWCurveConfig for PallasConfig {
    /// COEFF_A = 0
    const COEFF_A: Fq = Fq::ZERO;

    /// COEFF_B = 5
    const COEFF_B: Fq = MontFp!("5");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const GENERATOR: Affine = Affine::new_unchecked(G_GENERATOR_X, G_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

impl GLVConfig for PallasConfig {
    const ENDO_COEFFS: &'static [Self::BaseField] = &[MontFp!(
        "20444556541222657078399132219657928148671392403212669005631716460534733845831"
    )];

    const LAMBDA: Self::ScalarField =
        MontFp!("26005156700822196841419187675678338661165322343552424574062261873906994770353");

    const SCALAR_DECOMP_COEFFS: [(bool, <Self::ScalarField as PrimeField>::BigInt); 4] = [
        (false, BigInt!("98231058071100081932162823354453065728")),
        (true, BigInt!("98231058071186745657228807397848383489")),
        (false, BigInt!("196462116142286827589391630752301449217")),
        (false, BigInt!("98231058071100081932162823354453065728")),
    ];

    fn endomorphism(p: &Projective) -> Projective {
        // Endomorphism of the points on the curve.
        // endomorphism_p(x,y) = (BETA * x, y)
        // where BETA is a non-trivial cubic root of unity in Fq.
        let mut res = (*p).clone();
        res.x *= Self::ENDO_COEFFS[0];
        res
    }

    fn endomorphism_affine(p: &Affine) -> Affine {
        // Endomorphism of the points on the curve.
        // endomorphism_p(x,y) = (BETA * x, y)
        // where BETA is a non-trivial cubic root of unity in Fq.
        let mut res = (*p).clone();
        res.x *= Self::ENDO_COEFFS[0];
        res
    }
}

/// G_GENERATOR_X = -1
pub const G_GENERATOR_X: Fq = MontFp!("-1");

/// G_GENERATOR_Y = 2
pub const G_GENERATOR_Y: Fq = MontFp!("2");
