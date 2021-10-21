use ark_ff::{
    biginteger::{BigInteger256, BigInteger64},
    field_new,
    fields::{FftParameters, Fp384, Fp384Parameters, FpParameters, Fp256, Fp256Parameters, Fp64, Fp64Parameters},
};
use crate::{ModelParameters, models::SWModelParameters, AffineCurve};
use crate::short_weierstrass_jacobian::GroupAffine;
use crate::hashing::curve_maps::swu::{SWUParams, SWUMap};
use crate::hashing::curve_maps::wb::{WBParams, WBMap};
use super::map_to_curve_hasher::{MapToCurveBasedHasher, MapToCurve};
use crate::hashing::{map_to_curve_hasher::HashToField, field_hashers::DefaultFieldHasher, HashToCurve, HashToCurveError};

use ark_ff::{Zero, One, Field, PrimeField, SquareRootField};
use ark_std::vec::Vec;
use std::collections::HashMap;

use ark_poly::{Polynomial, UVPolynomial, univariate::{DensePolynomial}};

//use ark_bls12_377::Bls12_377;
//use ark_bl12_377::{
//    fields::{FQ_ONE, FQ_ZERO},
//    Fq, Fr,
//};

pub type F127 = Fp64<F127Parameters>;

pub struct F127Parameters;

impl Fp64Parameters for F127Parameters {}
impl FftParameters for F127Parameters {
    type BigInt = BigInteger64;

    // N = 126 => s = 1
    const TWO_ADICITY: u32 = 1;

    //sage: FF(3)^63
    //126
    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: BigInteger64 = BigInteger64([126]);
}

impl FpParameters for F127Parameters {
    /// MODULUS = 127
    #[rustfmt::skip]
    const MODULUS: BigInteger64 = BigInteger64([127]);

    const MODULUS_BITS: u32 = 7;

    const CAPACITY: u32 = Self::MODULUS_BITS - 1;

    const REPR_SHAVE_BITS: u32 = 64 - Self::MODULUS_BITS;

    // Nearst power of 2^64 to 127 is 0 so R = 1 but maybe they mean larger
    // otherwise square root panics
    //sage: FF(2^64)
    //2
    #[rustfmt::skip]
    const R: BigInteger64 = BigInteger64([2]);

    #[rustfmt::skip]
    const R2: BigInteger64 = BigInteger64([4]);

    // sage: R = Integers(2^64)
    // sage: R
    // Ring of integers modulo 18446744073709551616
    // sage: m = R(127)
    // sage: m^(-1)
    // 9150747060186627967
    // sage: -m^(-1) 
    // 9295997013522923649
    const INV: u64 = 9295997013522923649;

    // sage: FF(3).multiplicative_order()
    // 126
    /// GENERATOR = 3
    #[rustfmt::skip]
    const GENERATOR: BigInteger64 = BigInteger64([3]);

    #[rustfmt::skip]
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger64 = BigInteger64([63]);

    // T and T_MINUS_ONE_DIV_TWO, where MODULUS - 1 = 2^S * T
    // For T coprime to 2

    // T = (MODULUS - 1) / 2^S =
    // 12208678567578594777604504606729831043093128246378069236549469339647
    //sage: factor(127-1)
    //2 * 3^2 * 7
    //sage: (127-1)/2
    //63
    #[rustfmt::skip]
    const T: BigInteger64 = BigInteger64([63]);

    // (T - 1) / 2 =
    #[rustfmt::skip]
    const T_MINUS_ONE_DIV_TWO: BigInteger64 = BigInteger64([31]);
}

const F127_ZERO: F127 = field_new!(F127, "0");
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

    const XI : F127 = field_new!(F127, "-1");
    const ZETA: F127 = field_new!(F127, "3");
    const XI_ON_ZETA_SQRT: F127 = field_new!(F127, "14");

}

///test that field_new make a none zero element out of 1
#[test]
fn test_field_element_construction() {
    let a1 = F127::from(1);
    let a2 = F127::from(2);
    let a3 = F127::from(125);

    assert!(F127::from(0) == a2 + a3);
}
    

/// Testing checking the hashing parameters are sane
#[test]
fn chceking_the_hsahing_parameters() {
    ///check zeta is a non-square
    assert!(SquareRootField::legendre(&TestSWUMapToCurveParams::ZETA).is_qr() == false);
    
}

/// The point of the test is to get a  simpl SWU compatible curve
/// and make simple hash
#[test]
fn hash_arbitary_string_to_curve_swu() {
    use blake2::{VarBlake2b};

    let test_swu_to_curve_hasher = MapToCurveBasedHasher::<GroupAffine<TestSWUMapToCurveParams>, DefaultFieldHasher<VarBlake2b>, SWUMap<TestSWUMapToCurveParams>>::new(&[1]).unwrap();
    
    let hash_result = test_swu_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

    
    println!("{:?}, {:?}", hash_result, hash_result.x, );

    assert!(hash_result.x != field_new!(F127, "0"));

}

/// the test use a simple SWU compatible curve
/// and map the whole field to it. We observe the map behaviour. Specifically
/// The map is not constant and that everything can be mapped and nobody panics
#[test]
fn map_field_to_curve_swu() {
    let test_map_to_curve =  SWUMap::<TestSWUMapToCurveParams>::new_map_to_curve(&[0]).unwrap();

    let mut map_range : Vec<GroupAffine<TestSWUMapToCurveParams>> = vec![];
    for current_field_element in 0..127 {
        map_range.push(test_map_to_curve.map_to_curve(F127::from(current_field_element)).unwrap());
    }

    let mut counts = HashMap::new();

    let mode = map_range.iter().copied().max_by_key(|&n| {
        let count = counts.entry(n).or_insert(0);
        *count += 1;
        *count
    }).unwrap();

    println!("mode {} repeated {} times", mode, counts.get(&mode).unwrap());

    assert!(*counts.get(&mode).unwrap() != 127);
}

//Testing wb19 on  small curvse
// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite Field of size 127
// E : y^2 = x^3 + 3
// Isogeny map
// (10*x^18*y + 59*x^17*y + 41*x^16*y + 48*x^15*y - 7*x^14*y + 6*x^13*y + 5*x^12*y + 62*x^11*y + 12*x^10*y + 36*x^9*y - 49*x^8*y - 18*x^7*y - 63*x^6*y - 43*x^5*y - 60*x^4*y - 18*x^3*y + 30*x^2*y - 57*x*y - 34*y)/(x^18 + 44*x^17 - 63*x^16 + 52*x^15 + 3*x^14 + 38*x^13 - 30*x^12 + 11*x^11 - 42*x^10 - 13*x^9 - 46*x^8 - 61*x^7 - 16*x^6 - 55*x^5 + 18*x^4 + 23*x^3 - 24*x^2 - 18*x + 32)
struct TestSWU127MapToIsogenousCurveParams;

//first we define the isogenous curve
//sage: E_isogenous.order()
//127
impl ModelParameters for TestSWU127MapToIsogenousCurveParams {
    type BaseField = F127;
    type ScalarField = F127;
}

// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite Field of size 127
impl SWModelParameters for TestSWU127MapToIsogenousCurveParams {
    /// COEFF_A = 1
    const COEFF_A: F127 = field_new!(F127, "109");

    /// COEFF_B = 1
    #[rustfmt::skip]
    const COEFF_B: F127 = field_new!(F127, "124");

    const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
    const COFACTOR_INV: F127 = field_new!(F127, "1");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (field_new!(F127, "62"), field_new!(F127, "70"));
}

impl SWUParams for TestSWU127MapToIsogenousCurveParams {

    const XI : F127 = field_new!(F127, "-1");
    const ZETA: F127 = field_new!(F127, "3");
    const XI_ON_ZETA_SQRT: F127 = field_new!(F127, "14");

}

//The struct defining our parameters for the target curve
struct TestWBF127MapToCurveParams;

impl ModelParameters for TestWBF127MapToCurveParams {
    type BaseField = F127;
    type ScalarField = F127;
}

impl SWModelParameters for TestWBF127MapToCurveParams {
    /// COEFF_A = 1
    const COEFF_A: F127 = field_new!(F127, "0");

    /// COEFF_B = 1
    #[rustfmt::skip]
    const COEFF_B: F127 = field_new!(F127, "3");

    const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
    const COFACTOR_INV: F127 = field_new!(F127, "1");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (field_new!(F127, "62"), field_new!(F127, "70"));
}

fn isogeny_e2_e1(domain_point: GroupAffine<TestSWU127MapToIsogenousCurveParams>) -> Result<GroupAffine<TestWBF127MapToCurveParams>, HashToCurveError> {
    //psi_x: (-57*x^13 - 21*x^12 + 10*x^11 + 34*x^10 + 40*x^9 - 13*x^8 + 32*x^7 - 32*x^6 + 23*x^5 - 14*x^4 + 39*x^3 + 23*x^2 + 63*x + 4)/(x^12 - 13*x^11 + 11*x^10 - 33*x^9 - 30*x^8 + 30*x^7 + 34*x^6 - 44*x^5 + 63*x^4 - 20*x^3 - 10*x^2 + 31*x + 2)

    //psi_y: (10*x^18*y + 59*x^17*y + 41*x^16*y + 48*x^15*y - 7*x^14*y + 6*x^13*y + 5*x^12*y + 62*x^11*y + 12*x^10*y + 36*x^9*y - 49*x^8*y - 18*x^7*y - 63*x^6*y - 43*x^5*y - 60*x^4*y - 18*x^3*y + 30*x^2*y - 57*x*y - 34*y)/(x^18 + 44*x^17 - 63*x^16 + 52*x^15 + 3*x^14 + 38*x^13 - 30*x^12 + 11*x^11 - 42*x^10 - 13*x^9 - 46*x^8 - 61*x^7 - 16*x^6 - 55*x^5 + 18*x^4 + 23*x^3 - 24*x^2 - 18*x + 32)
    let psi_x : [Vec<u64>; 2] = [vec![70, 106, 10, 34, 40, 114, 32, 95, 23, 113, 39, 23, 63,  4], vec![0, 1, 114, 11, 94, 97, 30, 34, 83, 63, 107, 117, 31,  2]];
    let psi_y = [vec![10,  59, 41, 48, 120, 6, 5, 62, 12, 36, 78, 109, 64, 84, 67, 109, 30, 70,  93], vec![1, 44, 64, 52, 3, 38, 97, 11, 85, 114, 81, 66, 111, 72, 18, 23, 103, 109, 32]];

    let psi_x_num_field_elm : Vec<F127> = psi_x[0].iter().map(|cur_coeff| {F127::from(*cur_coeff as u64) }).collect();

    let psi_x_den_field_elm : Vec<F127> = psi_x[1].iter().map(|cur_coeff| {F127::from(*cur_coeff as u64) }).collect();

    let x_num : DensePolynomial<<TestSWU127MapToIsogenousCurveParams as ModelParameters>::BaseField> = <DensePolynomial<<TestSWU127MapToIsogenousCurveParams as ModelParameters>::BaseField>>::from_coefficients_slice(&psi_x_num_field_elm.as_slice());

    let x_den : DensePolynomial<<TestSWU127MapToIsogenousCurveParams as ModelParameters>::BaseField> = <DensePolynomial<<TestSWU127MapToIsogenousCurveParams as ModelParameters>::BaseField>>::from_coefficients_slice(&psi_x_den_field_elm.as_slice());
//let mut x_num = F127::from("0");
    //psi_x.iter().map(| curr_coeff | { x_num += F127::from(curr_coeff) * }
    let psi_y_num_field_elm : Vec<F127> = psi_y[0].iter().map(|cur_coeff| {F127::from(*cur_coeff as u64) }).collect();

    let psi_y_den_field_elm : Vec<F127> = psi_y[1].iter().map(|cur_coeff| {F127::from(*cur_coeff as u64) }).collect();

    let y_num : DensePolynomial<<TestSWU127MapToIsogenousCurveParams as ModelParameters>::BaseField> = <DensePolynomial<<TestSWU127MapToIsogenousCurveParams as ModelParameters>::BaseField>>::from_coefficients_slice(&psi_y_num_field_elm.as_slice());

    let y_den : DensePolynomial<<TestSWU127MapToIsogenousCurveParams as ModelParameters>::BaseField> = <DensePolynomial<<TestSWU127MapToIsogenousCurveParams as ModelParameters>::BaseField>>::from_coefficients_slice(&psi_y_den_field_elm.as_slice());

    let img_x = x_num.evaluate(&domain_point.x) / x_den.evaluate(&domain_point.x);
    let img_y = (y_num.evaluate(&domain_point.x) * domain_point.y) / y_den.evaluate(&domain_point.x);
    Ok(GroupAffine::<TestWBF127MapToCurveParams>::new(img_x, img_y, false))

}

// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite Field of size 127
impl WBParams for TestWBF127MapToCurveParams 
//where [(); ISO_DEG + 1]: Sized, [(); ISO_DEG*2 + 1]: Sized,
{
    type IsogenousCurve = TestSWU127MapToIsogenousCurveParams;

    const PHI_X_NOM: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[field_new!(F127, "70"), field_new!(F127, "106"), field_new!(F127, "10"), field_new!(F127, "34"), field_new!(F127, "40"), field_new!(F127, "114"), field_new!(F127, "32"), field_new!(F127, "95"), field_new!(F127, "23"), field_new!(F127, "113"), field_new!(F127, "39"), field_new!(F127, "23"), field_new!(F127, "63"), field_new!(F127, "4")];

    const PHI_X_DEN: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[field_new!(F127, "0"), field_new!(F127, "1"), field_new!(F127, "114"), field_new!(F127, "11"), field_new!(F127, "94"), field_new!(F127, "97"), field_new!(F127, "30"), field_new!(F127, "34"), field_new!(F127, "83"), field_new!(F127, "63"), field_new!(F127, "107"), field_new!(F127, "117"), field_new!(F127, "31"), field_new!(F127, "2")];
    
    const PHI_Y_NOM: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "10"), field_new!(F127, "59"), field_new!(F127, "41"), field_new!(F127, "48"), field_new!(F127, "120"), field_new!(F127, "6"), field_new!(F127, "5"), field_new!(F127, "62"), field_new!(F127, "12"), field_new!(F127, "36"), field_new!(F127, "78"), field_new!(F127, "109"), field_new!(F127, "64"), field_new!(F127, "84"), field_new!(F127, "67"), field_new!(F127, "109"), field_new!(F127, "30"), field_new!(F127, "70"), field_new!(F127, "93")];
                       
    const PHI_Y_DEN: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "0"), field_new!(F127, "44"), field_new!(F127, "64"), field_new!(F127, "52"), field_new!(F127, "3"), field_new!(F127, "38"), field_new!(F127, "97"), field_new!(F127, "11"), field_new!(F127, "85"), field_new!(F127, "114"), field_new!(F127, "81"), field_new!(F127, "66"), field_new!(F127, "111"), field_new!(F127, "72"), field_new!(F127, "18"), field_new!(F127, "23"), field_new!(F127, "103"), field_new!(F127, "109"), field_new!(F127, "32")];

    //const isogeny_map: fn(domain_point: GroupAffine<Self::IsogenousCurve>) -> Result<GroupAffine<Self>, HashToCurveError> = isogeny_e2_e1;

}

/// The point of the test is to get a  simpl SWU compatible curve
/// and make simple hash
#[test]
fn hash_arbitary_string_to_curve_wb() {
    use blake2::{VarBlake2b};

    let test_wb_to_curve_hasher = MapToCurveBasedHasher::<GroupAffine<TestWBF127MapToCurveParams>, DefaultFieldHasher<VarBlake2b>, WBMap<TestWBF127MapToCurveParams>>::new(&[1]).unwrap();
    
    let hash_result = test_wb_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");
    
    println!("the wb hash is: {:?}", hash_result);

    assert!(hash_result.x != field_new!(F127, "0"));

}

