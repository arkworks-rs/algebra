use core::ops::Neg;

use crate::bls12_381::*;
use ark_ec::{
    bls12,
    hashing::curve_maps::wb::WBParams,
    models::CurveConfig,
    short_weierstrass::{self, *},
    AffineCurve, ProjectiveCurve,
};
use ark_ff::{BigInt, Field, MontFp, Zero};

pub type G2Affine = bls12::G2Affine<crate::bls12_381::Parameters>;
pub type G2Projective = bls12::G2Projective<crate::bls12_381::Parameters>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Parameters;

impl CurveConfig for Parameters {
    type BaseField = Fq2;
    type ScalarField = Fr;

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
    const COFACTOR_INV: Fr = MontFp!(
        "26652489039290660355457965112010883481355318854675681319708643586776743290055"
    );
}

impl short_weierstrass::SWCurveConfig for Parameters {
    /// COEFF_A = [0, 0]
    const COEFF_A: Fq2 = Fq2::new(g1::Parameters::COEFF_A, g1::Parameters::COEFF_A);

    /// COEFF_B = [4, 4]
    const COEFF_B: Fq2 = Fq2::new(g1::Parameters::COEFF_B, g1::Parameters::COEFF_B);

    /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
    const GENERATOR: G2Affine = G2Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: &Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }

    fn is_in_correct_subgroup_assuming_on_curve(point: &G2Affine) -> bool {
        // Algorithm from Section 4 of https://eprint.iacr.org/2021/1130.
        //
        // Checks that [p]P = [X]P

        let mut x_times_point =
            point.mul_bigint(BigInt::new([crate::bls12_381::Parameters::X[0], 0, 0, 0]));
        if crate::bls12_381::Parameters::X_IS_NEGATIVE {
            x_times_point = -x_times_point;
        }

        let p_times_point = p_power_endomorphism(point);

        x_times_point.eq(&p_times_point)
    }

    #[inline]
    fn clear_cofactor(p: &G2Affine) -> G2Affine {
        // Based on Section 4.1 of https://eprint.iacr.org/2017/419.pdf
        // [h(ψ)]P = [x^2 − x − 1]P + [x − 1]ψ(P) + (ψ^2)(2P)

        // x = -15132376222941642752
        // When multiplying, use -c1 instead, and then negate the result. That's much
        // more efficient, since the scalar -c1 has less limbs and a much lower Hamming
        // weight.
        let x: &'static [u64] = crate::bls12_381::Parameters::X;
        let p_projective = p.into_projective();

        // [x]P
        let x_p = Parameters::mul_affine(p, &x).neg();
        // ψ(P)
        let psi_p = p_power_endomorphism(&p);
        // (ψ^2)(2P)
        let mut psi2_p2 = double_p_power_endomorphism(&p_projective.double());

        // tmp = [x]P + ψ(P)
        let mut tmp = x_p.clone();
        tmp.add_assign_mixed(&psi_p);

        // tmp2 = [x^2]P + [x]ψ(P)
        let mut tmp2: Projective<Parameters> = tmp;
        tmp2 = tmp2.mul_bigint(x).neg();

        // add up all the terms
        psi2_p2 += tmp2;
        psi2_p2 -= x_p;
        psi2_p2.add_assign_mixed(&-psi_p);
        (psi2_p2 - p_projective).into_affine()
    }
}

pub const G2_GENERATOR_X: Fq2 = Fq2::new(G2_GENERATOR_X_C0, G2_GENERATOR_X_C1);
pub const G2_GENERATOR_Y: Fq2 = Fq2::new(G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1);

/// G2_GENERATOR_X_C0 =
/// 352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160
#[rustfmt::skip]
pub const G2_GENERATOR_X_C0: Fq = MontFp!("352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160");

/// G2_GENERATOR_X_C1 =
/// 3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758
#[rustfmt::skip]
pub const G2_GENERATOR_X_C1: Fq = MontFp!("3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758");

/// G2_GENERATOR_Y_C0 =
/// 1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905
#[rustfmt::skip]
pub const G2_GENERATOR_Y_C0: Fq = MontFp!("1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905");

/// G2_GENERATOR_Y_C1 =
/// 927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582
#[rustfmt::skip]
pub const G2_GENERATOR_Y_C1: Fq = MontFp!("927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582");

// psi(x,y) = (x**p * PSI_X, y**p * PSI_Y) is the Frobenius composed
// with the quadratic twist and its inverse

// PSI_X = 1/(u+1)^((p-1)/3)
pub const P_POWER_ENDOMORPHISM_COEFF_0 : Fq2 = Fq2::new(
    FQ_ZERO,
    MontFp!(
       "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437"
    )
);

// PSI_Y = 1/(u+1)^((p-1)/2)
pub const P_POWER_ENDOMORPHISM_COEFF_1: Fq2 = Fq2::new(
    MontFp!(
       "2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530"),
    MontFp!(
       "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257")
);

pub const DOUBLE_P_POWER_ENDOMORPHISM: Fq2 = Fq2::new(
    MontFp!("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436"),
    FQ_ZERO
);

pub fn p_power_endomorphism(p: &Affine<Parameters>) -> Affine<Parameters> {
    // The p-power endomorphism for G2 is defined as follows:
    // 1. Note that G2 is defined on curve E': y^2 = x^3 + 4(u+1). To map a point
    // (x, y) in E' to (s, t) in E,    one set s = x / ((u+1) ^ (1/3)), t = y /
    // ((u+1) ^ (1/2)), because E: y^2 = x^3 + 4. 2. Apply the Frobenius
    // endomorphism (s, t) => (s', t'), another point on curve E,    where s' =
    // s^p, t' = t^p. 3. Map the point from E back to E'; that is,
    //    one set x' = s' * ((u+1) ^ (1/3)), y' = t' * ((u+1) ^ (1/2)).
    //
    // To sum up, it maps
    // (x,y) -> (x^p / ((u+1)^((p-1)/3)), y^p / ((u+1)^((p-1)/2)))
    // as implemented in the code as follows.

    let mut res = *p;
    res.x.frobenius_map(1);
    res.y.frobenius_map(1);

    let tmp_x = res.x;
    res.x.c0 = -P_POWER_ENDOMORPHISM_COEFF_0.c1 * &tmp_x.c1;
    res.x.c1 = P_POWER_ENDOMORPHISM_COEFF_0.c1 * &tmp_x.c0;
    res.y *= P_POWER_ENDOMORPHISM_COEFF_1;

    res
}

/// For a p-power endomorphism psi(P), compute psi(psi(P))
pub fn double_p_power_endomorphism(p: &Projective<Parameters>) -> Projective<Parameters> {
    let mut res = *p;

    res.x *= DOUBLE_P_POWER_ENDOMORPHISM;
    res.y = res.y.neg();

    res
}

// Parameters from the [IETF draft v16, section E.3](https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-16.html#name-3-isogeny-map-for-bls12-381).
impl WBParams for Parameters {
    type IsogenousCurve = g2_swu_iso::SwuIsoParameters;

    const PHI_X_NOM: &'static [<Self::IsogenousCurve as CurveConfig>::BaseField] = &[
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
    ];

    const PHI_X_DEN: &'static [<Self::IsogenousCurve as CurveConfig>::BaseField] = &[
        Fq2::new(
                   MontFp!("0"), 
                   MontFp!("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715")), 
        Fq2::new(
                   MontFp!("12"), 
                   MontFp!("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775")), 
        Fq2::new(
                   MontFp!("1"), 
                   MontFp!("0")),
    ];

    const PHI_Y_NOM: &'static [<Self::IsogenousCurve as CurveConfig>::BaseField] = &[
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
    ];

    const PHI_Y_DEN: &'static [<Self::IsogenousCurve as CurveConfig>::BaseField] = &[
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
    ];
}
