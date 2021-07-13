use crate::ed_on_bls12_381::{Fq, Fr};
use ark_ec::{
    models::{ModelParameters, MontgomeryModelParameters, TEModelParameters},
    twisted_edwards::{TEAffine, TEProjective},
};
use ark_ff::field_new;

pub type EdwardsAffine = TEAffine<EdwardsParameters>;
pub type EdwardsProjective = TEProjective<EdwardsParameters>;

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
pub struct EdwardsParameters;

impl ModelParameters for EdwardsParameters {
    type BaseField = Fq;
    type ScalarField = Fr;
}

impl TEModelParameters for EdwardsParameters {
    /// COEFF_A = -1
    #[rustfmt::skip]
    const COEFF_A: Fq = field_new!(Fq, "-1");

    /// COEFF_D = (10240/10241) mod q
    #[rustfmt::skip]
    const COEFF_D: Fq = field_new!(Fq, "19257038036680949359750312669786877991949435402254120286184196891950884077233");

    /// COFACTOR = 8
    const COFACTOR: &'static [u64] = &[8];

    /// COFACTOR^(-1) mod r =
    /// 819310549611346726241370945440405716213240158234039660170669895299022906775
    #[rustfmt::skip]
    const COFACTOR_INV: Fr = field_new!(Fr, "819310549611346726241370945440405716213240158234039660170669895299022906775");

    /// AFFINE_GENERATOR_COEFFS = (GENERATOR_X, GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) = (GENERATOR_X, GENERATOR_Y);

    type MontgomeryModelParameters = EdwardsParameters;

    /// Multiplication by `a` is simply negation here.
    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        -(*elem)
    }
}

impl MontgomeryModelParameters for EdwardsParameters {
    /// COEFF_A = 40962
    #[rustfmt::skip]
    const COEFF_A: Fq = field_new!(Fq, "40962");
    /// COEFF_B = -40964
    #[rustfmt::skip]
    const COEFF_B: Fq = field_new!(Fq, "-40964");

    type TEModelParameters = EdwardsParameters;
}

#[rustfmt::skip]
const GENERATOR_X: Fq = field_new!(Fq, "8076246640662884909881801758704306714034609987455869804520522091855516602923");
#[rustfmt::skip]
const GENERATOR_Y: Fq = field_new!(Fq, "13262374693698910701929044844600465831413122818447359594527400194675274060458");

#[cfg(test)]
mod tests {
    use ark_ec::Group;
    use ark_std::rand::Rng;
    use ark_std::test_rng;

    use crate::ed_on_bls12_381::*;

    use ark_algebra_test_templates::{curves::*, groups::*};

    #[test]
    fn test_projective_curve() {
        curve_tests::<EdwardsProjective>();

        edwards_tests::<EdwardsParameters>();
    }

    #[test]
    fn test_projective_group() {
        let mut rng = test_rng();
        let a = rng.gen();
        let b = rng.gen();
        for _i in 0..100 {
            group_test::<EdwardsProjective>(a, b);
        }
    }

    #[test]
    fn test_generator() {
        let generator = EdwardsProjective::generator();
        assert!(generator.is_on_curve());
        assert!(generator.is_in_correct_subgroup_assuming_on_curve());
    }

    #[test]
    fn test_montgomery_conversion() {
        montgomery_conversion_test::<EdwardsParameters>();
    }
}
