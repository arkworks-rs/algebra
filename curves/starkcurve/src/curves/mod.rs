// The parameters for the curve have been taken from
// https://github.com/starkware-libs/cairo/blob/main/corelib/src/ec.cairo
// https://docs.starknet.io/architecture/cryptography/

use crate::{Fq, Fr};
use ark_ec::{
    models::CurveConfig,
    short_weierstrass::{self as sw, SWCurveConfig},
};
use ark_ff::{Field, MontFp};

#[cfg(test)]
mod tests;

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct StarkCurveConfig;

impl CurveConfig for StarkCurveConfig {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x1];

    /// COFACTOR_INV = 1
    const COFACTOR_INV: Fr = Fr::ONE;
}

pub type Affine = sw::Affine<StarkCurveConfig>;
pub type Projective = sw::Projective<StarkCurveConfig>;

impl SWCurveConfig for StarkCurveConfig {
    const COEFF_A: Fq = Fq::ONE;

    const COEFF_B: Fq =
        MontFp!("3141592653589793238462643383279502884197169399375105820974944592307816406665");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const GENERATOR: Affine = Affine::new_unchecked(G_GENERATOR_X, G_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(elem: Self::BaseField) -> Self::BaseField {
        elem
    }

    /// Correctness:
    /// Substituting (0, 0) into the curve equation gives 0^2 = b.
    /// Since b is not zero, the point (0, 0) is not on the curve.
    /// Therefore, we can safely use (0, 0) as a flag for the zero point.
    type ZeroFlag = ();
}

pub const G_GENERATOR_X: Fq =
    MontFp!("874739451078007766457464989774322083649278607533249481151382481072868806602");

pub const G_GENERATOR_Y: Fq =
    MontFp!("152666792071518830868575557812948353041420400780739481342941381225525861407");
