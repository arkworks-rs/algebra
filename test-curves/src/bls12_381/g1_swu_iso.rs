use crate::bls12_381::*;
use ark_ec::hashing::curve_maps::swu::SWUParams;
use ark_ec::models::{
    short_weierstrass::{Affine, SWCurveConfig},
    CurveConfig,
};
use ark_ff::MontFp;

type G1Affine = Affine<SwuIsoParameters>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct SwuIsoParameters;

impl CurveConfig for SwuIsoParameters {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = (x - 1)^2 / 3  = 76329603384216526031706109802092473003
    const COFACTOR: &'static [u64] = &[0x8c00aaab0000aaab, 0x396c8c005555e156];

    /// COFACTOR_INV = COFACTOR^{-1} mod r
    /// = 52435875175126190458656871551744051925719901746859129887267498875565241663483
    #[rustfmt::skip]
    const COFACTOR_INV: Fr = MontFp!("52435875175126190458656871551744051925719901746859129887267498875565241663483");
}

// https://datatracker.ietf.org/doc/draft-irtf-cfrg-hash-to-curve/
// Hashing to Elliptic Curves
// 8.8.1.  BLS12-381 G1
// BLS12381G1_XMD:SHA-256_SSWU_RO_ is defined as follows:
// *  E': y'^2 = x'^3 + A' * x' + B', where
//      -  A' = 0x144698a3b8e9433d693a02c96d4982b0ea985383ee66a8d8e8981aefd881ac98936f8da0e0f97f5cf428082d584c1d
//      -  B' = 0x12e2908d11688030018b12e8753eee3b2016c1f0f24f4070a0b9c14fcef35ef55a23215a316ceaa5d1cc48e98e172be0
//      -  A' = 12190336318893619529228877361869031420615612348429846051986726275283378313155663745811710833465465981901188123677
//      -  B' = 2906670324641927570491258158026293881577086121416628140204402091718288198173574630967936031029026176254968826637280
//  *  Z: 11
impl SWCurveConfig for SwuIsoParameters {
    const COEFF_A: Fq = MontFp!("12190336318893619529228877361869031420615612348429846051986726275283378313155663745811710833465465981901188123677");

    #[rustfmt::skip]
    const COEFF_B: Fq = MontFp!("2906670324641927570491258158026293881577086121416628140204402091718288198173574630967936031029026176254968826637280");

    const GENERATOR: G1Affine = G1Affine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);
}

/// Lexicographically smallest, valid x-coordinate of a point P on the curve (with its corresponding y) multiplied by the cofactor.
/// P_x = 2
/// P_y = 658522096176515125667361255350269797307718222519385801637008089782287711363858559738763090642304321670226247205569
/// P = E(P_x, P_y)
/// G = P * COFACTOR
const G1_GENERATOR_X: Fq = MontFp!("1677416608493238977774703213729589714082762656433187746258164626835771660734158898989765932111853529350617333597651");
const G1_GENERATOR_Y: Fq = MontFp!("1405098061573104639413728190240719229571583960971553962991897960445246185035342568402755187331334546673157015627211");

impl SWUParams for SwuIsoParameters {
    // ZETA = 0xb as per the IETF draft.
    const ZETA: Fq = MontFp!("11");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_gen() {
        let gen: G1Affine = SwuIsoParameters::GENERATOR;
        assert!(gen.is_on_curve());
        assert!(gen.is_in_correct_subgroup_assuming_on_curve());
    }
}
