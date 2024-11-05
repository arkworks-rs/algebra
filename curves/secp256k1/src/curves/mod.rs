use ark_ec::{
    hashing::curve_maps::{
        swu::SWUConfig,
        wb::{IsogenyMap, WBConfig},
    },
    models::CurveConfig,
    short_weierstrass::{self as sw, SWCurveConfig},
};
use ark_ff::{AdditiveGroup, Field, MontFp, Zero};

use crate::{fq::Fq, fr::Fr};

#[cfg(test)]
mod tests;

pub type Affine = sw::Affine<Config>;
pub type Projective = sw::Projective<Config>;

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x1];

    /// COFACTOR_INV = COFACTOR^{-1} mod r = 1
    #[rustfmt::skip]
    const COFACTOR_INV: Fr =  Fr::ONE;
}

impl SWCurveConfig for Config {
    /// COEFF_A = 0
    const COEFF_A: Fq = Fq::ZERO;

    /// COEFF_B = 7
    const COEFF_B: Fq = MontFp!("7");

    /// GENERATOR = (G_GENERATOR_X, G_GENERATOR_Y)
    const GENERATOR: Affine = Affine::new_unchecked(G_GENERATOR_X, G_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

/// `secp256k1_XMD:SHA-256_SSWU_RO_` isogenous curve
pub struct ConfigIsogenous {}
impl CurveConfig for ConfigIsogenous {
    type BaseField = <Config as CurveConfig>::BaseField;
    type ScalarField = <Config as CurveConfig>::ScalarField;

    const COFACTOR: &'static [u64] = Config::COFACTOR;
    const COFACTOR_INV: Self::ScalarField = Config::COFACTOR_INV;
}
type TheIsoCurveAffine = sw::Affine<ConfigIsogenous>;
impl SWCurveConfig for ConfigIsogenous {
    const COEFF_A: Self::BaseField = MontFp!("0x3f8731abdd661adca08a5558f0f5d272e953d363cb6f0e5d405447c01a444533");
    const COEFF_B: Self::BaseField = MontFp!("1771");
    const GENERATOR: TheIsoCurveAffine = TheIsoCurveAffine::new_unchecked(
        MontFp!("75295888890003590383366995344834012177557063699577440394299653383124903397514"), 
        MontFp!("82553647407850972504999846303729620951309077682374043495922869307182479212755")
    );
    /* $ sage iso_values.sage 
    ** SECP256k1

    generator
    (55066263022277343669578718895168534326250603453777594175500187360389116729240 : 32670510020758816978083085130507043184471273380659243275938904335757337482424 : 1)
    isogenous generator
    (75295888890003590383366995344834012177557063699577440394299653383124903397514 : 82553647407850972504999846303729620951309077682374043495922869307182479212755 : 1)
    does it looks good?
    True */
}
impl SWUConfig for ConfigIsogenous {
    const ZETA: Self::BaseField = MontFp!("-11");
}

// Parameters from the [IETF draft v16, section E.3](https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-16.html#name-suites-for-secp256k1).
impl WBConfig for Config {
    type IsogenousCurve = ConfigIsogenous;

    const ISOGENY_MAP: IsogenyMap<'static, Self::IsogenousCurve, Self> = IsogenyMap {
        x_map_numerator: &[
            MontFp!("0x8e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38daaaaa8c7"),
            MontFp!("0x7d3d4c80bc321d5b9f315cea7fd44c5d595d2fc0bf63b92dfff1044f17c6581"),
            MontFp!("0x534c328d23f234e6e2a413deca25caece4506144037c40314ecbd0b53d9dd262"),
            MontFp!("0x8e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38daaaaa88c"),
        ],
        x_map_denominator: &[
            MontFp!("0xd35771193d94918a9ca34ccbb7b640dd86cd409542f8487d9fe6b745781eb49b"),
            MontFp!("0xedadc6f64383dc1df7c4b2d51b54225406d36b641f5e41bbc52a56612a8c6d14"),
            MontFp!("1"),
            MontFp!("0"),
        ],
        y_map_numerator: &[
            MontFp!("0x4bda12f684bda12f684bda12f684bda12f684bda12f684bda12f684b8e38e23c"),
            MontFp!("0xc75e0c32d5cb7c0fa9d0a54b12a0a6d5647ab046d686da6fdffc90fc201d71a3"),
            MontFp!("0x29a6194691f91a73715209ef6512e576722830a201be2018a765e85a9ecee931"),
            MontFp!("0x2f684bda12f684bda12f684bda12f684bda12f684bda12f684bda12f38e38d84"),
        ],
        y_map_denominator: &[
            MontFp!("0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffff93b"),
            MontFp!("0x7a06534bb8bdb49fd5e9e6632722c2989467c1bfc8e8d978dfb425d2685c2573"),
            MontFp!("0x6484aa716545ca2cf3a70c3fa8fe337e0a3d21162f0d6299a7bf8192bfd2a76f"),
            MontFp!("1"),
        ],
    };
}

/// G_GENERATOR_X =
/// 55066263022277343669578718895168534326250603453777594175500187360389116729240
pub const G_GENERATOR_X: Fq =
    MontFp!("55066263022277343669578718895168534326250603453777594175500187360389116729240");

/// G_GENERATOR_Y =
/// 32670510020758816978083085130507043184471273380659243275938904335757337482424
pub const G_GENERATOR_Y: Fq =
    MontFp!("32670510020758816978083085130507043184471273380659243275938904335757337482424");
