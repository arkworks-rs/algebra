use crate::{Fq, Fr};
use ark_ec::{
    hashing::curve_maps::elligator2::Elligator2Config,
    models::CurveConfig,
    short_weierstrass::{self, SWCurveConfig},
    twisted_edwards::{Affine, MontCurveConfig, Projective, TECurveConfig},
};
use ark_ff::{AdditiveGroup, Field, MontFp, One};

#[cfg(test)]
mod tests;

pub type EdwardsAffine = Affine<BandersnatchConfig>;
pub type EdwardsProjective = Projective<BandersnatchConfig>;

pub type SWAffine = short_weierstrass::Affine<BandersnatchConfig>;
pub type SWProjective = short_weierstrass::Projective<BandersnatchConfig>;

/// `bandersnatch` is an incomplete twisted Edwards curve. These curves have
/// equations of the form: ax² + y² = 1 + dx²y².
/// over some base finite field Fq.
///
/// bandersnatch's curve equation: -5x² + y² = 1 + dx²y²
///
/// q = 52435875175126190479447740508185965837690552500527637822603658699938581184513.
///
/// a = -5.
/// d = (138827208126141220649022263972958607803/
///     171449701953573178309673572579671231137) mod q
///   = 45022363124591815672509500913686876175488063829319466900776701791074614335719.
///
/// Sage script to calculate these:
///
/// ```text
/// q = 52435875175126190479447740508185965837690552500527637822603658699938581184513
/// Fq = GF(q)
/// d = (Fq(138827208126141220649022263972958607803)/Fq(171449701953573178309673572579671231137))
/// ```
/// These parameters and the sage script obtained from:
/// <https://github.com/asanso/Bandersnatch/>
///
/// bandersnatch also has a short Weierstrass curve form, following the
/// form: y² = x³ + A * x + B
/// where
///
/// A = 10773120815616481058602537765553212789256758185246796157495669123169359657269
/// B = 29569587568322301171008055308580903175558631321415017492731745847794083609535
///
/// Script to transfer between different curves are available
/// <https://github.com/zhenfeizhang/bandersnatch/blob/main/bandersnatch/script/bandersnatch.sage>
#[derive(Clone, Default, PartialEq, Eq)]
pub struct BandersnatchConfig;

pub type EdwardsConfig = BandersnatchConfig;
pub type SWConfig = BandersnatchConfig;

impl CurveConfig for BandersnatchConfig {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 4
    const COFACTOR: &'static [u64] = &[4];

    /// COFACTOR^(-1) mod r =
    /// 9831726595336160714896451345284868594481866920080427688839802480047265754601
    const COFACTOR_INV: Fr =
        MontFp!("9831726595336160714896451345284868594481866920080427688839802480047265754601");
}

impl TECurveConfig for BandersnatchConfig {
    /// COEFF_A = -5
    const COEFF_A: Fq = MontFp!("-5");

    /// COEFF_D = (138827208126141220649022263972958607803/
    /// 171449701953573178309673572579671231137) mod q
    const COEFF_D: Fq =
        MontFp!("45022363124591815672509500913686876175488063829319466900776701791074614335719");

    /// AFFINE_GENERATOR_COEFFS = (GENERATOR_X, GENERATOR_Y)
    const GENERATOR: EdwardsAffine = EdwardsAffine::new_unchecked(TE_GENERATOR_X, TE_GENERATOR_Y);

    type MontCurveConfig = BandersnatchConfig;

    /// Multiplication by `a` is multiply by `-5`.
    #[inline(always)]
    fn mul_by_a(elem: Self::BaseField) -> Self::BaseField {
        -(elem.double().double() + elem)
    }
}

impl MontCurveConfig for BandersnatchConfig {
    /// COEFF_A = 29978822694968839326280996386011761570173833766074948509196803838190355340952
    const COEFF_A: Fq =
        MontFp!("29978822694968839326280996386011761570173833766074948509196803838190355340952");

    /// COEFF_B = 25465760566081946422412445027709227188579564747101592991722834452325077642517
    const COEFF_B: Fq =
        MontFp!("25465760566081946422412445027709227188579564747101592991722834452325077642517");

    type TECurveConfig = BandersnatchConfig;
}

// The TE form generator is generated following Zcash's fashion:
//  "The generators of G1 and G2 are computed by finding the lexicographically
//   smallest valid x-coordinate, and its lexicographically smallest
//   y-coordinate and scaling it by the cofactor such that the result is not
//   the point at infinity."
// The SW form generator is the same TE generator converted into SW form,
// obtained from the scripts:
//   <https://github.com/zhenfeizhang/bandersnatch/blob/main/bandersnatch/script/bandersnatch.sage>

/// x coordinate for TE curve generator
pub const TE_GENERATOR_X: Fq =
    MontFp!("18886178867200960497001835917649091219057080094937609519140440539760939937304");

/// y coordinate for TE curve generator
pub const TE_GENERATOR_Y: Fq =
    MontFp!("19188667384257783945677642223292697773471335439753913231509108946878080696678");

/// x coordinate for SW curve generator
pub const SW_GENERATOR_X: Fq =
    MontFp!("30900340493481298850216505686589334086208278925799850409469406976849338430199");

/// y coordinate for SW curve generator
pub const SW_GENERATOR_Y: Fq =
    MontFp!("12663882780877899054958035777720958383845500985908634476792678820121468453298");

impl SWCurveConfig for BandersnatchConfig {
    /// COEFF_A = 10773120815616481058602537765553212789256758185246796157495669123169359657269
    const COEFF_A: Self::BaseField =
        MontFp!("10773120815616481058602537765553212789256758185246796157495669123169359657269");

    /// COEFF_B = 29569587568322301171008055308580903175558631321415017492731745847794083609535
    const COEFF_B: Self::BaseField =
        MontFp!("29569587568322301171008055308580903175558631321415017492731745847794083609535");

    /// generators
    const GENERATOR: SWAffine = SWAffine::new_unchecked(SW_GENERATOR_X, SW_GENERATOR_Y);

    /// Correctness:
    /// Substituting (0, 0) into the curve equation gives 0^2 = b.
    /// Since b is not zero, the point (0, 0) is not on the curve.
    /// Therefore, we can safely use (0, 0) as a flag for the zero point.
    type ZeroFlag = ();
}

// Elligator hash to curve Bandersnatch
// sage: find_z_ell2(GF(52435875175126190479447740508185965837690552500527637822603658699938581184513))
// 5
//
// sage: Fq = GF(52435875175126190479447740508185965837690552500527637822603658699938581184513)
// sage: 1/Fq(25465760566081946422412445027709227188579564747101592991722834452325077642517)^2
// sage: COEFF_A = Fq(29978822694968839326280996386011761570173833766074948509196803838190355340952)
// sage: COEFF_B = Fq(25465760566081946422412445027709227188579564747101592991722834452325077642517)
// sage: 1/COEFF_B^2
// 35484827650731063748396669747216844996598387089274032563585525486049249153249
// sage: COEFF_A/COEFF_B
// 22511181562295907836254750456843438087744031914659733450388350895537307167857
impl Elligator2Config for BandersnatchConfig {
    const Z: Fq = MontFp!("5");

    /// This must be equal to 1/(MontCurveConfig::COEFF_B)^2;
    const ONE_OVER_COEFF_B_SQUARE: Fq =
        MontFp!("35484827650731063748396669747216844996598387089274032563585525486049249153249");

    /// This must be equal to MontCurveConfig::COEFF_A/MontCurveConfig::COEFF_B;
    const COEFF_A_OVER_COEFF_B: Fq =
        MontFp!("22511181562295907836254750456843438087744031914659733450388350895537307167857");
}

// Constants used in mapping TE form to SW form and vice versa
//
// sage: q = 52435875175126190479447740508185965837690552500527637822603658699938581184513
// sage: Fq = GF(q)
// sage: MONT_A = 29978822694968839326280996386011761570173833766074948509196803838190355340952
// sage: MONT_B = 25465760566081946422412445027709227188579564747101592991722834452325077642517
// sage: MONT_A/Fq(3)
// 9992940898322946442093665462003920523391277922024982836398934612730118446984
// sage: Fq(1)/MONT_B
// 41180284393978236561320365279764246793818536543197771097409483252169927600582
const MONT_A_OVER_THREE: Fq =
    MontFp!("9992940898322946442093665462003920523391277922024982836398934612730118446984");
const MONT_B_INV: Fq =
    MontFp!("41180284393978236561320365279764246793818536543197771097409483252169927600582");

impl BandersnatchConfig {
    /// Map a point in TE form to its corresponding point on SW curve
    pub fn map_te_to_sw(point: EdwardsAffine) -> Option<SWAffine> {
        if point.is_zero() {
            return SWAffine::identity()
        }
        //First we map the point from the TE to Montgamory
        //edward to mont  ((1+y)/(1-y), (1+y)/(x(1-y)))
        let v_denom = <<BandersnatchConfig as CurveConfig>::BaseField as One>::one() - point.y;
        let w_denom = point.x - point.x * point.y;

        let v_denom_inv = v_denom.inverse()?;
        let w_denom_inv = w_denom.inverse()?;

        let v_w_num = <<BandersnatchConfig as CurveConfig>::BaseField as One>::one() + point.y;

        let v = v_w_num * v_denom_inv;
        let w = v_w_num * w_denom_inv;

        //now we are mapping the montgomery point to SW.
        //Mont->SW ((x+A/3)/B,y/B)

        let x = MONT_B_INV * (v + MONT_A_OVER_THREE);
        let y = MONT_B_INV * w;

        let point_on_sw_curve = SWAffine::new_unchecked(x, y);
        debug_assert!(
            point_on_sw_curve.is_on_curve(),
            "TE point mapped off the SW curve"
        );

        return Some(point_on_sw_curve);
    }

    pub fn map_sw_to_te(point: SWAffine) -> Option<EdwardsAffine> {
        if point.is_zero() {
            return EdwardsAffine::zero()
        }
        // First  we are mappyng the sw point to  montgamory point
        //SW->Mont by (Bx−A/3,By)
        let mx = <BandersnatchConfig as MontCurveConfig>::COEFF_B * point.x - MONT_A_OVER_THREE;
        let my = <BandersnatchConfig as MontCurveConfig>::COEFF_B * point.y;

        //Then we map the TE point to Montgamory
        // (x,y)↦(x/y,(x−1)/(x+1))
        let v_denom = my.inverse()?;
        let x_p_1 = mx + <<BandersnatchConfig as CurveConfig>::BaseField as One>::one();
        let w_denom = x_p_1.inverse()?;

        let v = mx * v_denom;
        let w = (mx - <<BandersnatchConfig as CurveConfig>::BaseField as One>::one()) * w_denom;

        let point_on_te_curve = EdwardsAffine::new_unchecked(v, w);
        debug_assert!(
            point_on_te_curve.is_on_curve(),
            "TE point mapped off the SW curve"
        );

        return Some(point_on_te_curve);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_ec::hashing::{
        curve_maps::elligator2::Elligator2Map, map_to_curve_hasher::MapToCurveBasedHasher,
        HashToCurve,
    };
    use ark_ff::field_hashers::DefaultFieldHasher;
    use sha2::Sha512;

    #[test]
    fn test_elligtor2_hash2curve_hashes_to_curve() {
        let test_elligator2_to_curve_hasher = MapToCurveBasedHasher::<
            Projective<BandersnatchConfig>,
            DefaultFieldHasher<Sha512, 128>,
            Elligator2Map<BandersnatchConfig>,
        >::new(&[1])
        .unwrap();

        let hash_result = test_elligator2_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

        assert!(
            hash_result.is_on_curve(),
            "hash results into a point off the curve"
        );
    }

    #[test]
    fn test_mapping_from_te_to_sw_curve() {
        let test_elligator2_to_curve_hasher = MapToCurveBasedHasher::<
            Projective<BandersnatchConfig>,
            DefaultFieldHasher<Sha512, 128>,
            Elligator2Map<BandersnatchConfig>,
        >::new(&[1])
        .unwrap();

        let hash_result = test_elligator2_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

        assert!(
            hash_result.is_on_curve(),
            "hash results into a point off the curve"
        );

        assert!(
            BandersnatchConfig::map_te_to_sw(hash_result)
                .expect("could not map the te point to sw form")
                .is_on_curve(),
            "hash results into a point off the curve"
        );
    }

    #[test]
    fn test_mapping_from_te_to_sw_to_te_curve() {
        let test_elligator2_to_curve_hasher = MapToCurveBasedHasher::<
            Projective<BandersnatchConfig>,
            DefaultFieldHasher<Sha512, 128>,
            Elligator2Map<BandersnatchConfig>,
        >::new(&[1])
        .unwrap();

        let hash_result = test_elligator2_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

        assert!(
            hash_result.is_on_curve(),
            "hash results into a point off the curve"
        );

        let sw_point = BandersnatchConfig::map_te_to_sw(hash_result)
            .expect("could not map the te point to sw form");
        assert!(
            sw_point.is_on_curve(),
            "hash results into a point off the curve"
        );

        let te_point = BandersnatchConfig::map_sw_to_te(sw_point)
            .expect("could not map the te point to sw form");
        assert!(
            te_point.is_on_curve(),
            "hash results into a point off the curve"
        );

        assert!(
            te_point == hash_result,
            "point mapped to sw form was re-mapped to a different point on te form"
        );
    }
}
