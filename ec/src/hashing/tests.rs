use crate::{
    hashing::{
        curve_maps::{
            swu::{SWUMap, SWUParams},
            wb::WBParams,
        },
        map_to_curve_hasher::MapToCurve,
    },
    models::SWModelParameters,
    short_weierstrass_jacobian::GroupAffine,
    ModelParameters,
};
use ark_ff::{
    biginteger::BigInteger64,
    field_new,
    fields::{FftParameters, Fp64, Fp64Parameters, FpParameters},
};

use ark_ff::SquareRootField;
use ark_std::vec::Vec;
use hashbrown::HashMap;

#[cfg(all(feature = "default", feature = "std"))]
use crate::hashing::{
    curve_maps::wb::WBMap, field_hashers::DefaultFieldHasher,
    map_to_curve_hasher::MapToCurveBasedHasher, HashToCurve,
};

pub type F127 = Fp64<F127Parameters>;

pub struct F127Parameters;

impl Fp64Parameters for F127Parameters {}
impl FftParameters for F127Parameters {
    type BigInt = BigInteger64;

    // N = 126 => s = 1
    const TWO_ADICITY: u32 = 1;

    // sage: FF(3)^63
    // 126
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

    // Nearst greater power of 2^64 (2^64R) to 127 is 0 so R = 1
    // sage: FF(2^64)
    // 2
    #[rustfmt::skip]
    const R: BigInteger64 = BigInteger64([2]);

    /// R2 = R^2 % Self::MODULUS
    #[rustfmt::skip]
    const R2: BigInteger64 = BigInteger64([4]);

    /// INV = -MODULUS^{-1} mod 2^64
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
    // Montgomery conversion 3 * 2 = 6 % 127
    /// GENERATOR = 3
    #[rustfmt::skip]
    const GENERATOR: BigInteger64 = BigInteger64([6]);

    /// (Self::MODULUS - 1) / 2
    #[rustfmt::skip]
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger64 = BigInteger64([63]);

    // T and T_MINUS_ONE_DIV_TWO, where MODULUS - 1 = 2^S * T
    // For T coprime to 2

    /// t for 2^s * t = MODULUS - 1
    // T = (MODULUS - 1) / 2^S =
    // 12208678567578594777604504606729831043093128246378069236549469339647
    // sage: factor(127-1)
    // 2 * 3^2 * 7
    // sage: (127-1)/2
    // 63
    #[rustfmt::skip]
    const T: BigInteger64 = BigInteger64([63]);

    // (T - 1) / 2 = (63 - 1)/2
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
impl SWModelParameters for TestSWUMapToCurveParams {
    /// COEFF_A = 1
    const COEFF_A: F127 = F127_ONE;

    /// COEFF_B = 1
    #[rustfmt::skip]
    const COEFF_B: F127 = field_new!(F127, "63");

    const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
    const COFACTOR_INV: F127 = F127_ONE;

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (field_new!(F127, "62"), field_new!(F127, "70"));
}

impl SWUParams for TestSWUMapToCurveParams {
    const XI: F127 = field_new!(F127, "-1");
    const ZETA: F127 = field_new!(F127, "3");
    const XI_ON_ZETA_SQRT: F127 = field_new!(F127, "13");
}

/// test that field_new make a none zero element out of 1
#[test]
fn test_field_element_construction() {
    let a1 = F127::from(1);
    let a2 = F127::from(2);
    let a3 = F127::from(125);

    assert!(F127::from(0) == a2 + a3);
    assert!(F127::from(0) == a2 * a1 + a3);
}

#[test]
fn test_field_division() {
    let num = F127::from(0x3d);
    let den = F127::from(0x7b);
    let num_on_den = F127::from(0x50);

    assert!(num / den == num_on_den);
}

/// Testing checking the hashing parameters are sane
/// check zeta is a non-square
#[test]
fn chceking_the_hsahing_parameters() {
    assert!(SquareRootField::legendre(&TestSWUMapToCurveParams::ZETA).is_qr() == false);
}

/// The point of the test is to get a  simpl SWU compatible curve
/// and make simple hash
#[cfg(all(feature = "default", feature = "std"))]
#[test]
fn hash_arbitary_string_to_curve_swu() {
    use blake2::VarBlake2b;

    let test_swu_to_curve_hasher = MapToCurveBasedHasher::<
        GroupAffine<TestSWUMapToCurveParams>,
        DefaultFieldHasher<VarBlake2b>,
        SWUMap<TestSWUMapToCurveParams>,
    >::new(&[1])
    .unwrap();

    let hash_result = test_swu_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

    #[cfg(feature = "std")]
    println!("{:?}, {:?}", hash_result, hash_result.x,);

    assert!(hash_result.x != F127_ZERO);
}

/// the test use a simple SWU compatible curve
/// and map the whole field to it. We observe the map behaviour. Specifically
/// The map is not constant and that everything can be mapped and nobody panics
#[test]
fn map_field_to_curve_swu() {
    let test_map_to_curve = SWUMap::<TestSWUMapToCurveParams>::new_map_to_curve(&[0]).unwrap();

    let mut map_range: Vec<GroupAffine<TestSWUMapToCurveParams>> = vec![];
    for current_field_element in 0..127 {
        map_range.push(
            test_map_to_curve
                .map_to_curve(F127::from(current_field_element as u64))
                .unwrap(),
        );
    }

    let mut counts = HashMap::new();

    let mode = map_range
        .iter()
        .copied()
        .max_by_key(|&n| {
            let count = counts.entry(n).or_insert(0);
            *count += 1;
            *count
        })
        .unwrap();

    #[cfg(feature = "std")]
    println!(
        "mode {} repeated {} times",
        mode,
        counts.get(&mode).unwrap()
    );

    assert!(*counts.get(&mode).unwrap() != 127);
}

/// Testing WB19 hashing on  small curvse
/// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite
/// Field of size 127
struct TestSWU127MapToIsogenousCurveParams;

/// First we define the isogenous curve
/// sage: E_isogenous.order()
/// 127
impl ModelParameters for TestSWU127MapToIsogenousCurveParams {
    type BaseField = F127;
    type ScalarField = F127;
}

/// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite
/// Field of size 127
impl SWModelParameters for TestSWU127MapToIsogenousCurveParams {
    /// COEFF_A = 109
    const COEFF_A: F127 = field_new!(F127, "109");

    /// COEFF_B = 124
    #[rustfmt::skip]
    const COEFF_B: F127 = field_new!(F127, "124");

    const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
    const COFACTOR_INV: F127 = F127_ONE;

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (field_new!(F127, "84"), field_new!(F127, "2"));
}

/// SWU parameters for E_isogenous
impl SWUParams for TestSWU127MapToIsogenousCurveParams {
    /// NON-SQUARE = - 1
    const XI: F127 = field_new!(F127, "-1");
    /// A Primitive Root of unity = 3
    const ZETA: F127 = field_new!(F127, "3");
    /// sqrt(Xi/Zeta)
    const XI_ON_ZETA_SQRT: F127 = field_new!(F127, "13");
}

/// The struct defining our parameters for the target curve of hashing
struct TestWBF127MapToCurveParams;

impl ModelParameters for TestWBF127MapToCurveParams {
    type BaseField = F127;
    type ScalarField = F127;
}

/// E: Elliptic Curve defined by y^2 = x^3 + 3 over Finite
/// Field of size 127
impl SWModelParameters for TestWBF127MapToCurveParams {
    /// COEFF_A = 0
    const COEFF_A: F127 = F127_ZERO;

    /// COEFF_B = 3
    #[rustfmt::skip]
    const COEFF_B: F127 = field_new!(F127, "3");

    const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
    const COFACTOR_INV: F127 = F127_ONE;

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (field_new!(F127, "62"), field_new!(F127, "70"));
}

/// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite
/// Field of size 127
/// With psi: E_isogenous -> E
/// psi = (psi_x(x,y), psi_y(x,y))
/// where
/// psi_x: (-57*x^13 - 21*x^12 + 10*x^11 + 34*x^10 + 40*x^9 -
/// 13*x^8 + 32*x^7 - 32*x^6 + 23*x^5 - 14*x^4 + 39*x^3 + 23*x^2 + 63*x +
/// 4)/(x^12 - 13*x^11 + 11*x^10 - 33*x^9 - 30*x^8 + 30*x^7 + 34*x^6 - 44*x^5 +
/// 63*x^4 - 20*x^3 - 10*x^2 + 31*x + 2)
///
/// psi_y: (10*x^18*y + 59*x^17*y + 41*x^16*y + 48*x^15*y - 7*x^14*y + 6*x^13*y +
/// 5*x^12*y + 62*x^11*y + 12*x^10*y + 36*x^9*y - 49*x^8*y - 18*x^7*y - 63*x^6*y
/// - 43*x^5*y - 60*x^4*y - 18*x^3*y + 30*x^2*y - 57*x*y - 34*y)/(x^18 + 44*x^17
/// - 63*x^16 + 52*x^15 + 3*x^14 + 38*x^13 - 30*x^12 + 11*x^11 - 42*x^10 - 13*x^9
/// - 46*x^8 - 61*x^7 - 16*x^6 - 55*x^5 + 18*x^4 + 23*x^3 - 24*x^2 - 18*x + 32)
impl WBParams for TestWBF127MapToCurveParams {
    type IsogenousCurve = TestSWU127MapToIsogenousCurveParams;

    const PHI_X_NOM: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[
        field_new!(F127, "4"),
        field_new!(F127, "63"),
        field_new!(F127, "23"),
        field_new!(F127, "39"),
        field_new!(F127, "-14"),
        field_new!(F127, "23"),
        field_new!(F127, "-32"),
        field_new!(F127, "32"),
        field_new!(F127, "-13"),
        field_new!(F127, "40"),
        field_new!(F127, "34"),
        field_new!(F127, "10"),
        field_new!(F127, "-21"),
        field_new!(F127, "-57"),
    ];

    const PHI_X_DEN: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[
        field_new!(F127, "2"),
        field_new!(F127, "31"),
        field_new!(F127, "-10"),
        field_new!(F127, "-20"),
        field_new!(F127, "63"),
        field_new!(F127, "-44"),
        field_new!(F127, "34"),
        field_new!(F127, "30"),
        field_new!(F127, "-30"),
        field_new!(F127, "-33"),
        field_new!(F127, "11"),
        field_new!(F127, "-13"),
        field_new!(F127, "1"),
    ];

    const PHI_Y_NOM: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[
        field_new!(F127, "-34"),
        field_new!(F127, "-57"),
        field_new!(F127, "30"),
        field_new!(F127, "-18"),
        field_new!(F127, "-60"),
        field_new!(F127, "-43"),
        field_new!(F127, "-63"),
        field_new!(F127, "-18"),
        field_new!(F127, "-49"),
        field_new!(F127, "36"),
        field_new!(F127, "12"),
        field_new!(F127, "62"),
        field_new!(F127, "5"),
        field_new!(F127, "6"),
        field_new!(F127, "-7"),
        field_new!(F127, "48"),
        field_new!(F127, "41"),
        field_new!(F127, "59"),
        field_new!(F127, "10"),
    ];

    const PHI_Y_DEN: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[
        field_new!(F127, "32"),
        field_new!(F127, "-18"),
        field_new!(F127, "-24"),
        field_new!(F127, "23"),
        field_new!(F127, "18"),
        field_new!(F127, "-55"),
        field_new!(F127, "-16"),
        field_new!(F127, "-61"),
        field_new!(F127, "-46"),
        field_new!(F127, "-13"),
        field_new!(F127, "-42"),
        field_new!(F127, "11"),
        field_new!(F127, "-30"),
        field_new!(F127, "38"),
        field_new!(F127, "3"),
        field_new!(F127, "52"),
        field_new!(F127, "-63"),
        field_new!(F127, "44"),
        field_new!(F127, "1"),
    ];
}

/// The point of the test is to get a simpl SWU compatible curve
/// and make simple hash
#[cfg(all(feature = "default", feature = "std"))]
#[test]
fn hash_arbitary_string_to_curve_wb() {
    use blake2::VarBlake2b;

    let test_wb_to_curve_hasher = MapToCurveBasedHasher::<
        GroupAffine<TestWBF127MapToCurveParams>,
        DefaultFieldHasher<VarBlake2b>,
        WBMap<TestWBF127MapToCurveParams>,
    >::new(&[1])
    .unwrap();

    let hash_result = test_wb_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

    #[cfg(feature = "std")]
    println!("the wb hash is: {:?}", hash_result);

    assert!(hash_result.x != F127_ZERO);
}
