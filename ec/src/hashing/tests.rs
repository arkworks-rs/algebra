use ark_ff::{
    biginteger::{BigInteger256, BigInteger64},
    field_new,
    fields::{FftParameters, Fp384, Fp384Parameters, FpParameters, Fp256, Fp256Parameters, Fp64, Fp64Parameters},
};
use crate::{ModelParameters, models::SWModelParameters, AffineCurve};
use crate::short_weierstrass_jacobian::GroupAffine;
use crate::hashing::curve_maps::swu::{SWUParams, SWUMap};
use super::map_to_curve_hasher::MapToCurveBasedHasher;
use crate::hashing::{map_to_curve_hasher::HashToField, field_hashers::DefaultFieldHasher,HashToCurve};


pub type F127 = Fp64<F127Parameters>;

pub struct F127Parameters;

impl Fp64Parameters for F127Parameters {}
impl FftParameters for F127Parameters {
    type BigInt = BigInteger64;

    const TWO_ADICITY: u32 = 1;

    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: BigInteger64 = BigInteger64([1]);
}

impl FpParameters for F127Parameters {
    /// MODULUS = 127
    #[rustfmt::skip]
    const MODULUS: BigInteger64 = BigInteger64([127]);

    const MODULUS_BITS: u32 = 8;

    const CAPACITY: u32 = Self::MODULUS_BITS - 1;

    const REPR_SHAVE_BITS: u32 = 1;

    #[rustfmt::skip]
    const R: BigInteger64 = BigInteger64([0]);

    #[rustfmt::skip]
    const R2: BigInteger64 = BigInteger64([0]);

    // sage: R = Integers(2^64)
    // sage: R
    // Ring of integers modulo 18446744073709551616
    // sage: m = R(127)
    // sage: m^(-1)
    // 9150747060186627967
    // sage: -m^(-1) 
    // 9295997013522923649
    const INV: u64 = 9295997013522923649;

    /// GENERATOR = 3
    #[rustfmt::skip]
    const GENERATOR: BigInteger64 = BigInteger64([3]);

    #[rustfmt::skip]
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger64 = BigInteger64([63]);

    // T and T_MINUS_ONE_DIV_TWO, where MODULUS - 1 = 2^S * T
    // For T coprime to 2

    // T = (MODULUS - 1) / 2^S =
    // 12208678567578594777604504606729831043093128246378069236549469339647
    #[rustfmt::skip]
    const T: BigInteger64 = BigInteger64([63]);

    // (T - 1) / 2 =
    #[rustfmt::skip]
    const T_MINUS_ONE_DIV_TWO: BigInteger64 = BigInteger64([31]);
}

const F127_ZERO: F127 = field_new!(F127, "3");
const F127_ONE: F127 = field_new!(F127, "1");

struct TestSWUMapToCurveParams;

impl ModelParameters for TestSWUMapToCurveParams {
    type BaseField = F127;
    type ScalarField = F127;
}
/// just because not defining another field
///
/// from itertools import product
/// p = 127
/// FF = GF(p)
/// for a,b in product(range(0,p), range(0,p)):
///     try:
///         E = EllipticCurve([FF(a),FF(b)])
///         if E.order() == p:
///             print(E)
///     except:
///         pass
/// 
/// y^2 = x^3 + x + 63
///
impl SWModelParameters for TestSWUMapToCurveParams {
    /// COEFF_A = 1
    const COEFF_A: F127 = field_new!(F127, "1");

    /// COEFF_B = 1
    #[rustfmt::skip]
    const COEFF_B: F127 = field_new!(F127, "63");

    const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
    const COFACTOR_INV: F127 = field_new!(F127, "1");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (field_new!(F127, "62"), field_new!(F127, "70"));


}
impl SWUParams for TestSWUMapToCurveParams {


    const XI : F127 = field_new!(F127, "126");
    const ZETA: F127 = field_new!(F127, "2");
    const XI_ON_ZETA_SQRT: F127 = field_new!(F127, "95");

}

/// The point of the test is to get a  simplest SWU compatible curve
/// and hash the whole field to it. We observe the map behavoir. Specifically
/// The map is not constant
#[test]
fn map_whole_small_field_to_curve_swu() {
    use blake2::{VarBlake2b};
        
    let test_swu_to_curve_hasher = MapToCurveBasedHasher::<GroupAffine<TestSWUMapToCurveParams>, DefaultFieldHasher<VarBlake2b>, SWUMap<TestSWUMapToCurveParams>>::new(&[1]).unwrap();

    let hash_result = test_swu_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").unwrap();

    println!("{:?}, {:?}", hash_result.x, field_new!(F127, "1") );

    assert!(hash_result.x != field_new!(F127, "1"));

}
