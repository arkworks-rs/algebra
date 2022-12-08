use crate::secp256k1::{Fq, Fr};
use ark_ec::{models::CurveConfig, short_weierstrass::*};
use ark_ff::{Field, MontFp, Zero};

pub type G1Affine = Affine<Parameters>;
pub type G1Projective = Projective<Parameters>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Parameters;

impl CurveConfig for Parameters {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x1];

    /// COFACTOR_INV = COFACTOR^{-1} mod r = 1
    #[rustfmt::skip]
    const COFACTOR_INV: Fr =  Fr::ONE;
}

impl SWCurveConfig for Parameters {
    /// COEFF_A = 0
    const COEFF_A: Fq = Fq::ZERO;

    /// COEFF_B = 7
    const COEFF_B: Fq = MontFp!("7");

    /// GENERATOR = (G_GENERATOR_X, G_GENERATOR_Y)
    const GENERATOR: G1Affine = Affine::new_unchecked(G_GENERATOR_X, G_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

/// G_GENERATOR_X = 55066263022277343669578718895168534326250603453777594175500187360389116729240
pub const G_GENERATOR_X: Fq =
    MontFp!("55066263022277343669578718895168534326250603453777594175500187360389116729240");

/// G_GENERATOR_Y = 32670510020758816978083085130507043184471273380659243275938904335757337482424
pub const G_GENERATOR_Y: Fq =
    MontFp!("32670510020758816978083085130507043184471273380659243275938904335757337482424");
