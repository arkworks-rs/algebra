use crate::*;

use ark_ec::{
    hashing::curve_maps::{swu::SWUConfig, wb::IsogenyMap},
    models::{
        short_weierstrass::{Affine, SWCurveConfig},
        CurveConfig,
    },
};
use ark_ff::MontFp;

type G2Affine = Affine<SwuIsoConfig>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct SwuIsoConfig;

impl CurveConfig for SwuIsoConfig {
    type BaseField = Fq2;
    type ScalarField = Fr;

    /// Cofactors of g2_iso and g2 are the same.
    /// COFACTOR = (x^8 - 4 x^7 + 5 x^6) - (4 x^4 + 6 x^3 - 4 x^2 - 4 x + 13) //
    /// 9
    /// = 3055023339312683442009997531931215042144660192541881426676640329822676041829718840265074273592599778478322728390416166612858038233783720963550777062779109
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
    const COFACTOR_INV: Fr =
        MontFp!("26652489039290660355457965112010883481355318854675681319708643586776743290055");
}

// https://datatracker.ietf.org/doc/draft-irtf-cfrg-hash-to-curve/
// Hashing to Elliptic Curves
// 8.8.2.  BLS12-381 G2
//   * E': y'^2 = x'^3 + A' * x' + B', where
//
//      - A' = 240 * I
//
//      - B' = 1012 * (1 + I)
//
//   * Z: -(2 + I)
impl SWCurveConfig for SwuIsoConfig {
    /// COEFF_A = 240 * I
    const COEFF_A: Fq2 = Fq2::new(MontFp!("0"), MontFp!("240"));

    /// COEFF_B = 1012 + 1012 * I
    const COEFF_B: Fq2 = Fq2::new(MontFp!("1012"), MontFp!("1012"));

    const GENERATOR: G2Affine = G2Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);
}

/// Lexicographically smallest, valid x-coordinate of a point P on the curve
/// (with its corresponding y) multiplied by the cofactor. P_x = 1
/// P_y = 1199519624119946820355795551601605892701128025883245860600494152840508171012839086684258857614063467038089173303263 + 2721622435888802346851223931977585460571674503470326381323808470905804676865417627238564067834747838523978879375704 * I
/// P = E(P_x, P_y)
/// G = P * COFACTOR
const G2_GENERATOR_X: Fq2 = Fq2::new(
    MontFp!("2595569946714414516067015540153643524656442638788025933727967960306287756885400469291119095920626560658971252184199"),
    MontFp!("1037079738597573406765355774006601850633656296583542639082316151670128374872040593053087014315526494961765370307992")
);
const G2_GENERATOR_Y: Fq2 = Fq2::new(
    MontFp!("3927929472994661655038722055497331445175131868678630546921475383290711810401295661250673209427965906654429357114487"),
    MontFp!("3300326318345570015758639333209189167876318321385223785506096497597561910823001330832964776707374262378602791224889")
);

impl SWUConfig for SwuIsoConfig {
    // ZETA = -(2 + u) as per IETF draft.
    const ZETA: Fq2 = Fq2::new(MontFp!("-2"), MontFp!("-1"));
}

pub const ISOGENY_MAP_TO_G2  : IsogenyMap<'_, SwuIsoConfig, g2::Config> = IsogenyMap {
    x_map_numerator: &[
        Fq2::new(
                   MontFp!("889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542"),
                   MontFp!("889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542")),
        Fq2::new(
                   MontFp!("0"),
                   MontFp!("2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706522")),
        Fq2::new(
                   MontFp!("2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706526"),
                   MontFp!("1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853261")),
        Fq2::new(
                   MontFp!("3557697382419259905260257622876359250272784728834673675850718343221361467102966990615722337003569479144794908942033"),
                   MontFp!("0")),
    ],

    x_map_denominator:  &[
        Fq2::new(
                   MontFp!("0"),
                   MontFp!("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715")),
        Fq2::new(
                   MontFp!("12"),
                   MontFp!("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775")),
        Fq2::new(
                   MontFp!("1"),
                   MontFp!("0")),
    ],

    y_map_numerator: &[
        Fq2::new(
                   MontFp!("3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558"),
                   MontFp!("3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558")),
        Fq2::new(
                   MontFp!("0"),
                   MontFp!("889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235518")),
        Fq2::new(
                   MontFp!("2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706524"),
                   MontFp!("1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853263")),
        Fq2::new(
                   MontFp!("2816510427748580758331037284777117739799287910327449993381818688383577828123182200904113516794492504322962636245776"),
                   MontFp!("0")),
    ],

    y_map_denominator: &[
        Fq2::new(
                   MontFp!("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355"),
                   MontFp!("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355")),
        Fq2::new(
                   MontFp!("0"),
                   MontFp!("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559571")),
        Fq2::new(
                   MontFp!("18"),
                   MontFp!("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559769")),
        Fq2::new(
                   MontFp!("1"),
                   MontFp!("0")),
    ],
};

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_gen() {
        let gen: G2Affine = curves::g2_swu_iso::SwuIsoConfig::GENERATOR;
        assert!(gen.is_on_curve());
        assert!(gen.is_in_correct_subgroup_assuming_on_curve());
    }
}
