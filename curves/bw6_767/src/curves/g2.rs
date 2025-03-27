use ark_ec::{
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
    short_weierstrass::{Affine, Projective},
};
use ark_ff::{AdditiveGroup, MontFp};

use crate::{Fq, Fr};

pub type G2Affine = Affine<Config>;
pub type G2Projective = Projective<Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR =
    /// 124074696211871689196744963988542244365937182994917792082847997279938522233341057826255097957635256182243502012934833
    const COFACTOR: &'static [u64] = &[
        0x9fed0006fffaaab1,
        0xfae29bffb34d7c0d,
        0xc51e35fba8145036,
        0x58c9927410ca3a62,
        0x7772b64205a0bc67,
        0x26212b5cf67cecaf,
        0x3,
    ];

    /// COFACTOR^(-1) mod r =
    /// 1034808299677096100380606582404873291173913026971901593767142419502683535585229274705219741821274468081298550569313
    const COFACTOR_INV: Fr = MontFp!("1034808299677096100380606582404873291173913026971901593767142419502683535585229274705219741821274468081298550569313");
}

impl SWCurveConfig for Config {
    /// COEFF_A = 0
    const COEFF_A: Fq = Fq::ZERO;

    /// COEFF_B = 4
    const COEFF_B: Fq = MontFp!("3");

    /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
    const GENERATOR: G2Affine = G2Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_elem: Self::BaseField) -> Self::BaseField {
        use ark_ff::Zero;
        Self::BaseField::zero()
    }
}

/// G2_GENERATOR_X =
///  370611171465172359348863648443534520144617072349884185652206813771489664034831143983178049920510836078361116088420840622225267322852644540540617123958979924966938307707664543525950567252218300954395355151658118858470703533448342222
pub const G2_GENERATOR_X: Fq = MontFp!("370611171465172359348863648443534520144617072349884185652206813771489664034831143983178049920510836078361116088420840622225267322852644540540617123958979924966938307707664543525950567252218300954395355151658118858470703533448342222");

/// G2_GENERATOR_Y =
/// 455144308204607096185992716699045373884508292978508084510087807751472279103896568109582325400258900176330927780121791269969939391813736974371796892558810828460226121428602798229282770695472612961143258458821149661074127679136388603
pub const G2_GENERATOR_Y: Fq = MontFp!("455144308204607096185992716699045373884508292978508084510087807751472279103896568109582325400258900176330927780121791269969939391813736974371796892558810828460226121428602798229282770695472612961143258458821149661074127679136388603");
