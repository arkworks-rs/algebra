use crate::ed_on_bls12_381::{Fq, Fr};
use ark_ec::{
    models::CurveConfig,
    twisted_edwards::{self, MontCurveConfig, TECurveConfig},
};
use ark_ff::MontFp;

pub type Affine = twisted_edwards::Affine<EdwardsConfig>;
pub type Projective = twisted_edwards::Projective<EdwardsConfig>;

/// `JubJub` is a twisted Edwards curve. These curves have equations of the
/// form: ax² + y² = 1 - dx²y².
/// over some base finite field Fq.
///
/// JubJub's curve equation: -x² + y² = 1 - (10240/10241)x²y²
///
/// q = 52435875175126190479447740508185965837690552500527637822603658699938581184513.
///
/// a = -1.
/// d = (10240/10241) mod q
///   = 19257038036680949359750312669786877991949435402254120286184196891950884077233.
///
/// Sage script to calculate these:
///
/// ```text
/// q = 52435875175126190479447740508185965837690552500527637822603658699938581184513
/// Fq = GF(q)
/// d = -(Fq(10240)/Fq(10241))
/// ```
/// These parameters and the sage script obtained from:
/// <https://github.com/zcash/zcash/issues/2230#issuecomment-317182190>
#[derive(Clone, Default, PartialEq, Eq)]
pub struct EdwardsConfig;

impl CurveConfig for EdwardsConfig {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 8
    const COFACTOR: &'static [u64] = &[8];

    /// COFACTOR^(-1) mod r =
    /// 819310549611346726241370945440405716213240158234039660170669895299022906775
    #[rustfmt::skip]
    const COFACTOR_INV: Fr = MontFp!("819310549611346726241370945440405716213240158234039660170669895299022906775");
}

impl TECurveConfig for EdwardsConfig {
    const COEFF_A: Fq = MontFp!("-1");

    /// COEFF_D = (10240/10241) mod q
    const COEFF_D: Fq =
        MontFp!("19257038036680949359750312669786877991949435402254120286184196891950884077233");

    const GENERATOR: twisted_edwards::Affine<Self> =
        twisted_edwards::Affine::new_unchecked(GENERATOR_X, GENERATOR_Y);

    type MontCurveConfig = EdwardsConfig;

    /// Multiplication by `a` is simply negation here.
    #[inline(always)]
    fn mul_by_a(elem: Self::BaseField) -> Self::BaseField {
        -elem
    }
}

impl MontCurveConfig for EdwardsConfig {
    const COEFF_A: Fq = MontFp!("40962");
    const COEFF_B: Fq = MontFp!("-40964");

    type TECurveConfig = EdwardsConfig;
}

const GENERATOR_X: Fq =
    MontFp!("8076246640662884909881801758704306714034609987455869804520522091855516602923");
const GENERATOR_Y: Fq =
    MontFp!("13262374693698910701929044844600465831413122818447359594527400194675274060458");
