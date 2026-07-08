use crate::{fq::Fq, fr::Fr};
use ark_ec::{
    models::CurveConfig,
    scalar_mul::glv::{GLVConfig, GLVFastDecomp},
    short_weierstrass::{self as sw, SWCurveConfig},
    AffineRepr,
};
use ark_ff::{AdditiveGroup, BigInt, Field, MontFp, PrimeField, Zero};

#[cfg(test)]
mod tests;

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct VestaConfig;

impl CurveConfig for VestaConfig {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x1];

    /// COFACTOR_INV = 1
    const COFACTOR_INV: Fr = Fr::ONE;
}

pub type Affine = sw::Affine<VestaConfig>;
pub type Projective = sw::Projective<VestaConfig>;

impl SWCurveConfig for VestaConfig {
    /// COEFF_A = 0
    const COEFF_A: Fq = Fq::ZERO;

    /// COEFF_B = 5
    const COEFF_B: Fq = MontFp!("5");

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

    #[inline]
    fn mul_projective(base: &sw::Projective<Self>, scalar: &[u64]) -> sw::Projective<Self> {
        let s = Self::ScalarField::from_sign_and_limbs(true, scalar);
        GLVConfig::glv_mul_projective(*base, s)
    }

    #[inline]
    fn mul_affine(base: &sw::Affine<Self>, scalar: &[u64]) -> sw::Projective<Self> {
        let s = Self::ScalarField::from_sign_and_limbs(true, scalar);
        <Self as GLVConfig>::glv_mul_projective(base.into_group(), s)
    }
}

impl GLVConfig for VestaConfig {
    const ENDO_COEFFS: &'static [Self::BaseField] = &[MontFp!(
        "26005156700822196841419187675678338661165322343552424574062261873906994770353"
    )];

    const LAMBDA: Self::ScalarField =
        MontFp!("20444556541222657078399132219657928148671392403212669005631716460534733845831");

    const SCALAR_DECOMP_COEFFS: [(bool, <Self::ScalarField as PrimeField>::BigInt); 4] = [
        (false, BigInt!("98231058071100081932162823354453065729")),
        (true, BigInt!("98231058071186745657228807397848383488")),
        (false, BigInt!("196462116142286827589391630752301449217")),
        (false, BigInt!("98231058071100081932162823354453065729")),
    ];

    // Constants for the allocation-free decomposition, derived from
    // `SCALAR_DECOMP_COEFFS` by `scripts/glv_fast_decomp.py`. `g1`/`g2` are
    // `round(2^384 * |n22|/r)` and `round(2^384 * |n12|/r)`; `a22`/`a12` are
    // `|n22|`/`|n12|`; and `negate_k2` holds since `sign(n12)*sign(n22) = -1`.
    const FAST_DECOMP: Option<GLVFastDecomp<Self::ScalarField>> = Some(GLVFastDecomp {
        g1: &[
            0x841414c24bf99a83,
            0x61afdea685cc1578,
            0x32c49e4c00000003,
            0x279a745902a2654e,
            0x0000000000000001,
        ],
        g2: &[
            0x0009789fdd747ae0,
            0x61afdea6853283ae,
            0xff2b871bffffffff,
            0x279a745903c12455,
            0x0000000000000001,
        ],
        a12: MontFp!("98231058071186745657228807397848383488"),
        a22: MontFp!("98231058071100081932162823354453065729"),
        negate_k2: true,
    });

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
/// Encoded in Montgomery form, so the value here is -R mod p.
pub const G_GENERATOR_X: Fq = MontFp!("-1");

/// G_GENERATOR_Y = 2
/// Encoded in Montgomery form, so the value here is 2R mod p.
pub const G_GENERATOR_Y: Fq = MontFp!("2");
