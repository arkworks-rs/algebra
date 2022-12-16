use crate::bls12_381::*;
use ark_ec::{
    hashing::curve_maps::wb::{IsogenyMap, WBConfig},
    models::CurveConfig,
    short_weierstrass::{self, *},
};
use ark_ff::{MontFp, Zero};

pub type G1Affine = Affine<Config>;
pub type G1Projective = Projective<Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = (x - 1)^2 / 3  = 76329603384216526031706109802092473003
    const COFACTOR: &'static [u64] = &[0x8c00aaab0000aaab, 0x396c8c005555e156];

    /// COFACTOR_INV = COFACTOR^{-1} mod r
    /// = 52435875175126190458656871551744051925719901746859129887267498875565241663483
    #[rustfmt::skip]
    const COFACTOR_INV: Fr = MontFp!("52435875175126190458656871551744051925719901746859129887267498875565241663483");
}

impl short_weierstrass::SWCurveConfig for Config {
    /// COEFF_A = 0
    const COEFF_A: Fq = MontFp!("0");

    /// COEFF_B = 4
    #[rustfmt::skip]
    const COEFF_B: Fq = MontFp!("4");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const GENERATOR: G1Affine = G1Affine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }

    #[inline]
    fn clear_cofactor(p: &G1Affine) -> G1Affine {
        // Using the effective cofactor, as explained in
        // Section 5 of https://eprint.iacr.org/2019/403.pdf.
        //
        // It is enough to multiply by (x - 1), instead of (x - 1)^2 / 3
        // sqrt(76329603384216526031706109802092473003*3) = 15132376222941642753
        let h_eff: &[u64] = &[0xd201000000010001];
        Config::mul_affine(p, h_eff).into()
    }
}

// Config from the [IETF draft v16, section E.2](https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-16.html#name-11-isogeny-map-for-bls12-381).
impl WBConfig for Config {
    type IsogenousCurve = g1_swu_iso::SwuIsoConfig;

    const ISOGENY_MAP: IsogenyMap<'static, Self::IsogenousCurve, Self> =
        g1_swu_iso::ISOGENY_MAP_TO_G1;
}

/// G1_GENERATOR_X =
/// 3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507
#[rustfmt::skip]
pub const G1_GENERATOR_X: Fq = MontFp!("3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507");

/// G1_GENERATOR_Y =
/// 1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569
#[rustfmt::skip]
pub const G1_GENERATOR_Y: Fq = MontFp!("1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569");

#[cfg(test)]
mod test {
    use super::*;
    use ark_ec::CurveGroup;
    use ark_std::UniformRand;

    #[test]
    fn batch_normalization() {
        let mut rng = ark_std::test_rng();

        let mut g_s = [G1Projective::zero(); 100];
        for i in 0..100 {
            g_s[i] = G1Projective::rand(&mut rng);
        }

        let mut g_s_affine_naive = [G1Affine::identity(); 100];
        for (i, g) in g_s.iter().enumerate() {
            g_s_affine_naive[i] = g.into_affine();
        }

        let g_s_affine_fast = G1Projective::normalize_batch(&g_s);
        assert_eq!(g_s_affine_naive.as_ref(), g_s_affine_fast.as_slice());
    }
}
