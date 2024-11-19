use ark_ec::{
    bls12,
    bls12::Bls12Config,
    hashing::curve_maps::wb::{IsogenyMap, WBConfig},
    scalar_mul::glv::GLVConfig,
    short_weierstrass::{Affine, Projective, SWCurveConfig},
    AffineRepr, CurveConfig, CurveGroup, PrimeGroup,
};

use ark_ff::{AdditiveGroup, BigInt, Field, MontFp, PrimeField, Zero};

use crate::*;

use super::g2_swu_iso::{SwuIsoConfig, ISOGENY_MAP_TO_G2};

pub type G2Affine = bls12::G2Affine<crate::Config>;
pub type G2Projective = bls12::G2Projective<crate::Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq2;
    type ScalarField = Fr;

    /// COFACTOR =
    /// 7923214915284317143930293550643874566881017850177945424769256759165301436616933228209277966774092486467289478618404761412630691835764674559376407658497
    #[rustfmt::skip]
    const COFACTOR: &'static [u64] = &[
        0x0000000000000001,
        0x452217cc90000000,
        0xa0f3622fba094800,
        0xd693e8c36676bd09,
        0x8c505634fae2e189,
        0xfbb36b00e1dcc40c,
        0xddd88d99a6f6a829,
        0x26ba558ae9562a,
    ];

    /// COFACTOR_INV = COFACTOR^{-1} mod r
    /// = 6764900296503390671038341982857278410319949526107311149686707033187604810669
    const COFACTOR_INV: Fr =
        MontFp!("6764900296503390671038341982857278410319949526107311149686707033187604810669");
}

impl SWCurveConfig for Config {
    /// COEFF_A = [0, 0]
    const COEFF_A: Fq2 = Fq2::new(g1::Config::COEFF_A, g1::Config::COEFF_A);

    // As per https://eprint.iacr.org/2012/072.pdf,
    // this curve has b' = b/i, where b is the COEFF_B of G1, and x^6 -i is
    // the irreducible poly used to extend from Fp2 to Fp12.
    // In our case, i = u (App A.3, T_6).
    /// COEFF_B = [0,
    /// 155198655607781456406391640216936120121836107652948796323930557600032281009004493664981332883744016074664192874906]
    const COEFF_B: Fq2 = Fq2::new(
        Fq::ZERO,
        MontFp!("155198655607781456406391640216936120121836107652948796323930557600032281009004493664981332883744016074664192874906"),
    );

    /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
    const GENERATOR: G2Affine = G2Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }

    #[inline]
    fn clear_cofactor(p: &G2Affine) -> G2Affine {
        // Based on Section 4.1 of https://eprint.iacr.org/2017/419.pdf
        // [h(ψ)]P = [x^2 − x − 1]P + [x − 1]ψ(P) + (ψ^2)(2P)

        let x: &'static [u64] = crate::Config::X;
        let p_projective = p.into_group();

        // [x]P
        let x_p = Config::mul_affine(p, x);
        // ψ(P)
        let psi_p = p_power_endomorphism(p);
        // (ψ^2)(2P)
        let mut psi2_p2 = double_p_power_endomorphism(&p_projective.double());

        // tmp = [x]P + ψ(P)
        let mut tmp = x_p;
        tmp += &psi_p;

        // tmp2 = [x^2]P + [x]ψ(P)
        let mut tmp2: Projective<Config> = tmp;
        tmp2 = tmp2.mul_bigint(x);

        // add up all the terms
        psi2_p2 += tmp2;
        psi2_p2 -= x_p;
        psi2_p2 += &-psi_p;
        (psi2_p2 - p_projective).into_affine()
    }
}

impl GLVConfig for Config {
    const ENDO_COEFFS: &'static[Self::BaseField] = &[
        Fq2::new(
            MontFp!("258664426012969093929703085429980814127835149614277183275038967946009968870203535512256352201271898244626862047231"),
            Fq::ZERO
        )
    ];

    const LAMBDA: Self::ScalarField = MontFp!("91893752504881257701523279626832445440");

    const SCALAR_DECOMP_COEFFS: [(bool, <Self::ScalarField as PrimeField>::BigInt); 4] = [
        (false, BigInt!("91893752504881257701523279626832445440")),
        (true, BigInt!("1")),
        (false, BigInt!("1")),
        (false, BigInt!("91893752504881257701523279626832445441")),
    ];

    fn endomorphism(p: &Projective<Self>) -> Projective<Self> {
        let mut res = (*p).clone();
        res.x *= Self::ENDO_COEFFS[0];
        res
    }

    fn endomorphism_affine(p: &Affine<Self>) -> Affine<Self> {
        let mut res = (*p).clone();
        res.x *= Self::ENDO_COEFFS[0];
        res
    }
}

pub const G2_GENERATOR_X: Fq2 = Fq2::new(G2_GENERATOR_X_C0, G2_GENERATOR_X_C1);
pub const G2_GENERATOR_Y: Fq2 = Fq2::new(G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1);

/// G2_GENERATOR_X_C0 =
/// 233578398248691099356572568220835526895379068987715365179118596935057653620464273615301663571204657964920925606294
pub const G2_GENERATOR_X_C0: Fq = MontFp!("233578398248691099356572568220835526895379068987715365179118596935057653620464273615301663571204657964920925606294");

/// G2_GENERATOR_X_C1 =
/// 140913150380207355837477652521042157274541796891053068589147167627541651775299824604154852141315666357241556069118
pub const G2_GENERATOR_X_C1: Fq = MontFp!("140913150380207355837477652521042157274541796891053068589147167627541651775299824604154852141315666357241556069118");

/// G2_GENERATOR_Y_C0 =
/// 63160294768292073209381361943935198908131692476676907196754037919244929611450776219210369229519898517858833747423
pub const G2_GENERATOR_Y_C0: Fq = MontFp!("63160294768292073209381361943935198908131692476676907196754037919244929611450776219210369229519898517858833747423");

/// G2_GENERATOR_Y_C1 =
/// 149157405641012693445398062341192467754805999074082136895788947234480009303640899064710353187729182149407503257491
pub const G2_GENERATOR_Y_C1: Fq = MontFp!("149157405641012693445398062341192467754805999074082136895788947234480009303640899064710353187729182149407503257491");

// PSI_X = u^((p-1)/3)
const P_POWER_ENDOMORPHISM_COEFF_0 : Fq2 = Fq2::new(
    MontFp!(
        "80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410946"
    ),
    Fq::ZERO,
);

// PSI_Y = u^((p-1)/2)
const P_POWER_ENDOMORPHISM_COEFF_1: Fq2 = Fq2::new(
    MontFp!(
        "216465761340224619389371505802605247630151569547285782856803747159100223055385581585702401816380679166954762214499"),
        Fq::ZERO,
    );

// PSI_2_X = u^((p^2 - 1)/3)
const DOUBLE_P_POWER_ENDOMORPHISM_COEFF_0: Fq2 = Fq2::new(
        MontFp!("80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410945"),
        Fq::ZERO
    );

/// psi(x,y) is the untwist-Frobenius-twist endomorhism on E'(Fq2)
fn p_power_endomorphism(p: &Affine<Config>) -> Affine<Config> {
    // The p-power endomorphism for G2 is defined as follows:
    // 1. Note that G2 is defined on curve E': y^2 = x^3 + 1/u.
    //    To map a point (x, y) in E' to (s, t) in E,
    //    one set s = x * (u ^ (1/3)), t = y * (u ^ (1/2)),
    //    because E: y^2 = x^3 + 1.
    // 2. Apply the Frobenius endomorphism (s, t) => (s', t'),
    //    another point on curve E, where s' = s^p, t' = t^p.
    // 3. Map the point from E back to E'; that is,
    //    one set x' = s' / ((u) ^ (1/3)), y' = t' / ((u) ^ (1/2)).
    //
    // To sum up, it maps
    // (x,y) -> (x^p * (u ^ ((p-1)/3)), y^p * (u ^ ((p-1)/2)))
    // as implemented in the code as follows.

    let mut res = *p;
    res.x.frobenius_map_in_place(1);
    res.y.frobenius_map_in_place(1);

    res.x *= P_POWER_ENDOMORPHISM_COEFF_0;
    res.y *= P_POWER_ENDOMORPHISM_COEFF_1;

    res
}

/// For a p-power endomorphism psi(P), compute psi(psi(P))
fn double_p_power_endomorphism(p: &Projective<Config>) -> Projective<Config> {
    // p_power_endomorphism(&p_power_endomorphism(&p.into_affine())).into()
    let mut res = *p;

    res.x *= DOUBLE_P_POWER_ENDOMORPHISM_COEFF_0;
    // u^((p^2 - 1)/2) == -1
    res.y = -res.y;

    res
}

impl WBConfig for Config {
    type IsogenousCurve = SwuIsoConfig;

    const ISOGENY_MAP: IsogenyMap<'static, Self::IsogenousCurve, Self> = ISOGENY_MAP_TO_G2;
}

#[cfg(test)]
mod test {

    use super::*;
    use ark_std::{rand::Rng, UniformRand};

    fn sample_unchecked() -> Affine<g2::Config> {
        let mut rng = ark_std::test_rng();
        loop {
            let x1 = Fq::rand(&mut rng);
            let x2 = Fq::rand(&mut rng);
            let greatest = rng.gen();
            let x = Fq2::new(x1, x2);

            if let Some(p) = Affine::get_point_from_x_unchecked(x, greatest) {
                return p;
            }
        }
    }

    #[test]
    fn test_psi_2() {
        let p = sample_unchecked();
        let psi_p = p_power_endomorphism(&p);
        let psi2_p_composed = p_power_endomorphism(&psi_p);
        let psi2_p_optimised = double_p_power_endomorphism(&p.into());

        assert_eq!(psi2_p_composed, psi2_p_optimised);
    }

    #[test]
    fn test_cofactor_clearing() {
        let h_eff = &[
            0x1e34800000000000,
            0xcf664765b0000003,
            0x8e8e73ad8a538800,
            0x78ba279637388559,
            0xb85860aaaad29276,
            0xf7ee7c4b03103b45,
            0x8f6ade35a5c7d769,
            0xa951764c46f4edd2,
            0x53648d3d9502abfb,
            0x1f60243677e306,
        ];
        const SAMPLES: usize = 10;
        for _ in 0..SAMPLES {
            let p: Affine<g2::Config> = sample_unchecked();
            let optimised = p.clear_cofactor();
            let naive = g2::Config::mul_affine(&p, h_eff);
            assert_eq!(optimised.into_group(), naive);
            assert!(optimised.is_on_curve());
            assert!(optimised.is_in_correct_subgroup_assuming_on_curve());
        }
    }
}
