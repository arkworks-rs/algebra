use crate::bls12_381::*;
use ark_ec::models::{
    short_weierstrass::{Affine, SWCurveConfig},
    CurveConfig,
};
use ark_ff::MontFp;

use ark_ec::hashing::curve_maps::swu::SWUParams;

type G2Affine = Affine<SwuIsoParameters>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct SwuIsoParameters;

impl CurveConfig for SwuIsoParameters {
    type BaseField = Fq2;
    type ScalarField = Fr;

    /// Cofactors of g2_iso and g2 are the same.
    /// COFACTOR = (x^8 - 4 x^7 + 5 x^6) - (4 x^4 + 6 x^3 - 4 x^2 - 4 x + 13) //
    /// 9
    /// = 305502333931268344200999753193121504214466019254188142667664032982267604182971884026507427359259977847832272839041616661285803823378372096355777062779109
    #[rustfmt::skip]
    const COFACTOR: &'static [u64] = &[
        0xcf1c38e31c7238e5,
        0x1616ec6e786f0c70,
        0x21537e293a6691ae,
        0xa628f1cb4d9e82ef,
        0xa68a205b2e5a7ddf,
        0xcd91de4547085aba,
        0x91d50792876a202,
        0x5d543a95414e7f1,
    ];

    /// COFACTOR_INV = COFACTOR^{-1} mod r
    /// 26652489039290660355457965112010883481355318854675681319708643586776743290055
    #[rustfmt::skip]
    const COFACTOR_INV: Fr = MontFp!("26652489039290660355457965112010883481355318854675681319708643586776743290055");
}

// https://datatracker.ietf.org/doc/draft-irtf-cfrg-hash-to-curve/
// Hashing to Elliptic Curves
// 8.8.2.  BLS12-381 G2
//   *  E': y'^2 = x'^3 + A' * x' + B', where
//
//      -  A' = 240 * I
//
//      -  B' = 1012 * (1 + I)
//
//   * Z: -(2 + I)
impl SWCurveConfig for SwuIsoParameters {
    /// COEFF_A = 240 * I
    const COEFF_A: Fq2 = Fq2::new(MontFp!("0"), MontFp!("240"));

    /// COEFF_B = 1012 + 1012 * I
    const COEFF_B: Fq2 = Fq2::new(MontFp!("1012"), MontFp!("1012"));

    const GENERATOR: G2Affine = G2Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);
}

/// Lexicographically smallest, valid x-coordinate of a point P on the curve (with its corresponding y) multiplied by the cofactor.
/// P_x = 1
/// P_y = 1199519624119946820355795551601605892701128025883245860600494152840508171012839086684258857614063467038089173303263 + 2721622435888802346851223931977585460571674503470326381323808470905804676865417627238564067834747838523978879375704 * I
/// P = E(P_x, P_y)
/// G = P * COFACTOR
const G2_GENERATOR_X: Fq2 = Fq2::new(G2_GENERATOR_X_C0, G2_GENERATOR_X_C1);
const G2_GENERATOR_Y: Fq2 = Fq2::new(G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1);

const G2_GENERATOR_X_C0: Fq = MontFp!("2595569946714414516067015540153643524656442638788025933727967960306287756885400469291119095920626560658971252184199");
const G2_GENERATOR_X_C1: Fq = MontFp!("1037079738597573406765355774006601850633656296583542639082316151670128374872040593053087014315526494961765370307992");
const G2_GENERATOR_Y_C0: Fq = MontFp!("3927929472994661655038722055497331445175131868678630546921475383290711810401295661250673209427965906654429357114487");
const G2_GENERATOR_Y_C1: Fq = MontFp!("3300326318345570015758639333209189167876318321385223785506096497597561910823001330832964776707374262378602791224889");

impl SWUParams for SwuIsoParameters {
    // ZETA = -(2 + u) as per IETF draft.
    const ZETA: Fq2 = Fq2::new(MontFp!("-2"), MontFp!("-1"));
}
#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_gen() {
        let gen: G2Affine = g2_swu_iso::SwuIsoParameters::GENERATOR;
        assert!(gen.is_on_curve());
        assert!(gen.is_in_correct_subgroup_assuming_on_curve());
    }
}
