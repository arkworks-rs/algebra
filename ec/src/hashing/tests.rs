use crate::{
    hashing::{
        curve_maps::{
            swu::{parity, SWUMap, SWUParams},
            wb::{WBMap, WBParams},
        },
        field_hashers::DefaultFieldHasher,
        map_to_curve_hasher::{MapToCurve, MapToCurveBasedHasher},
        HashToCurve,
    },
    models::SWModelParameters,
    short_weierstrass_jacobian::GroupAffine,
    ModelParameters,
};
use ark_ff::{biginteger::BigInteger64, fields::Fp64, BigInt, MontBackend, MontFp};

use ark_ff::SquareRootField;
use ark_std::vec::Vec;
use ark_test_curves::bls12_381::{Fq, Fq2, Fq6};
use hashbrown::HashMap;

pub struct F127Config;
pub type F127 = Fp64<MontBackend<F127Config, 1>>;

impl ark_ff::MontConfig<1> for F127Config {
    // sage: FF(3)^63
    // 126
    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: F127 = MontFp!(F127, "126");

    /// MODULUS = 127
    #[rustfmt::skip]
    const MODULUS: BigInteger64 = BigInt!("127");

    // sage: FF(3).multiplicative_order()
    // 126
    // Montgomery conversion 3 * 2 = 6 % 127
    /// GENERATOR = 3
    #[rustfmt::skip]
    const GENERATOR: F127 = MontFp!(F127, "6");

    // T and T_MINUS_ONE_DIV_TWO, where MODULUS - 1 = 2^S * T
    // For T coprime to 2
}

const F127_ZERO: F127 = MontFp!(F127, "0");
const F127_ONE: F127 = MontFp!(F127, "1");

struct TestSWUMapToCurveParams;

impl ModelParameters for TestSWUMapToCurveParams {
    const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
    const COFACTOR_INV: F127 = F127_ONE;

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
    const COEFF_B: F127 = MontFp!(F127, "63");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (MontFp!(F127, "62"), MontFp!(F127, "70"));
}

impl SWUParams for TestSWUMapToCurveParams {
    const XI: F127 = MontFp!(F127, "-1");
    const ZETA: F127 = MontFp!(F127, "3");
    const XI_ON_ZETA_SQRT: F127 = MontFp!(F127, "13");
}

/// test that MontFp make a none zero element out of 1
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

/// Check that the hashing parameters are sane: zeta should be a non-square
#[test]
fn checking_the_hashing_parameters() {
    assert!(SquareRootField::legendre(&TestSWUMapToCurveParams::ZETA).is_qr() == false);
}

/// The point of the test is to get a simple SWU compatible curve and make
/// simple hash
#[test]
fn hash_arbitary_string_to_curve_swu() {
    use blake2::Blake2bVar;

    let test_swu_to_curve_hasher = MapToCurveBasedHasher::<
        GroupAffine<TestSWUMapToCurveParams>,
        DefaultFieldHasher<Blake2bVar, 128>,
        SWUMap<TestSWUMapToCurveParams>,
    >::new(&[1])
    .unwrap();

    let hash_result = test_swu_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

    assert!(
        hash_result.is_on_curve(),
        "hash results into a point off the curve"
    );
}

/// Use a simple SWU compatible curve and map the whole field to it. We observe
/// the map behaviour. Specifically, the map should be non-constant, all
/// elements should be mapped to curve successfully. everything can be mapped
#[test]
fn map_field_to_curve_swu() {
    let test_map_to_curve = SWUMap::<TestSWUMapToCurveParams>::new_map_to_curve().unwrap();

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

    assert!(
        *counts.get(&mode).unwrap() != 127,
        "a constant hash function is not good."
    );
}

/// Testing WB19 hashing on a small curve
/// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite
/// Field of size 127
/// Isogenous to E : y^2 = x^3 + 3
struct TestSWU127MapToIsogenousCurveParams;

/// First we define the isogenous curve
/// sage: E_isogenous.order()
/// 127
impl ModelParameters for TestSWU127MapToIsogenousCurveParams {
    const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
    const COFACTOR_INV: F127 = F127_ONE;

    type BaseField = F127;
    type ScalarField = F127;
}

/// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite
/// Field of size 127
impl SWModelParameters for TestSWU127MapToIsogenousCurveParams {
    /// COEFF_A = 109
    const COEFF_A: F127 = MontFp!(F127, "109");

    /// COEFF_B = 124
    #[rustfmt::skip]
    const COEFF_B: F127 = MontFp!(F127, "124");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (MontFp!(F127, "84"), MontFp!(F127, "2"));
}

/// SWU parameters for E_isogenous
impl SWUParams for TestSWU127MapToIsogenousCurveParams {
    /// NON-SQUARE = - 1
    const XI: F127 = MontFp!(F127, "-1");
    /// A Primitive Root of unity = 3
    const ZETA: F127 = MontFp!(F127, "3");
    /// sqrt(Xi/Zeta)
    const XI_ON_ZETA_SQRT: F127 = MontFp!(F127, "13");
}

/// The struct defining our parameters for the target curve of hashing
struct TestWBF127MapToCurveParams;

impl ModelParameters for TestWBF127MapToCurveParams {
    const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
    const COFACTOR_INV: F127 = F127_ONE;

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
    const COEFF_B: F127 = MontFp!(F127, "3");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (MontFp!(F127, "62"), MontFp!(F127, "70"));
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
        MontFp!(F127, "4"),
        MontFp!(F127, "63"),
        MontFp!(F127, "23"),
        MontFp!(F127, "39"),
        MontFp!(F127, "-14"),
        MontFp!(F127, "23"),
        MontFp!(F127, "-32"),
        MontFp!(F127, "32"),
        MontFp!(F127, "-13"),
        MontFp!(F127, "40"),
        MontFp!(F127, "34"),
        MontFp!(F127, "10"),
        MontFp!(F127, "-21"),
        MontFp!(F127, "-57"),
    ];

    const PHI_X_DEN: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[
        MontFp!(F127, "2"),
        MontFp!(F127, "31"),
        MontFp!(F127, "-10"),
        MontFp!(F127, "-20"),
        MontFp!(F127, "63"),
        MontFp!(F127, "-44"),
        MontFp!(F127, "34"),
        MontFp!(F127, "30"),
        MontFp!(F127, "-30"),
        MontFp!(F127, "-33"),
        MontFp!(F127, "11"),
        MontFp!(F127, "-13"),
        MontFp!(F127, "1"),
    ];

    const PHI_Y_NOM: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[
        MontFp!(F127, "-34"),
        MontFp!(F127, "-57"),
        MontFp!(F127, "30"),
        MontFp!(F127, "-18"),
        MontFp!(F127, "-60"),
        MontFp!(F127, "-43"),
        MontFp!(F127, "-63"),
        MontFp!(F127, "-18"),
        MontFp!(F127, "-49"),
        MontFp!(F127, "36"),
        MontFp!(F127, "12"),
        MontFp!(F127, "62"),
        MontFp!(F127, "5"),
        MontFp!(F127, "6"),
        MontFp!(F127, "-7"),
        MontFp!(F127, "48"),
        MontFp!(F127, "41"),
        MontFp!(F127, "59"),
        MontFp!(F127, "10"),
    ];

    const PHI_Y_DEN: &'static [<Self::IsogenousCurve as ModelParameters>::BaseField] = &[
        MontFp!(F127, "32"),
        MontFp!(F127, "-18"),
        MontFp!(F127, "-24"),
        MontFp!(F127, "23"),
        MontFp!(F127, "18"),
        MontFp!(F127, "-55"),
        MontFp!(F127, "-16"),
        MontFp!(F127, "-61"),
        MontFp!(F127, "-46"),
        MontFp!(F127, "-13"),
        MontFp!(F127, "-42"),
        MontFp!(F127, "11"),
        MontFp!(F127, "-30"),
        MontFp!(F127, "38"),
        MontFp!(F127, "3"),
        MontFp!(F127, "52"),
        MontFp!(F127, "-63"),
        MontFp!(F127, "44"),
        MontFp!(F127, "1"),
    ];
}

/// The point of the test is to get a simple WB compatible curve
/// and make simple hash
#[test]
fn hash_arbitary_string_to_curve_wb() {
    use blake2::Blake2bVar;

    let test_wb_to_curve_hasher = MapToCurveBasedHasher::<
        GroupAffine<TestWBF127MapToCurveParams>,
        DefaultFieldHasher<Blake2bVar, 128>,
        WBMap<TestWBF127MapToCurveParams>,
    >::new(&[1])
    .unwrap();

    let hash_result = test_wb_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

    assert!(
        hash_result.x != F127_ZERO && hash_result.y != F127_ZERO,
        "we assume that not both a and b coefficienst are zero for the test curve"
    );

    assert!(
        hash_result.is_on_curve(),
        "hash results into a point off the curve"
    );
}

#[test]
fn test_parity_of_prime_field_elements() {
    let a1 = Fq::from(0);
    let a2 = Fq::from(1);
    let a3 = Fq::from(10);
    assert_eq!(parity(&a1), false);
    assert_eq!(parity(&a2), true);
    assert_eq!(parity(&a3), false);
}

#[test]
fn test_parity_of_quadratic_extension_elements() {
    let element_test1 = Fq2::new(Fq::from(0), Fq::from(1));
    let element_test2 = Fq2::new(Fq::from(1), Fq::from(0));
    let element_test3 = Fq2::new(Fq::from(10), Fq::from(5));
    let element_test4 = Fq2::new(Fq::from(5), Fq::from(10));
    assert_eq!(parity(&element_test1), true, "parity is the oddness of first non-zero coefficient of element represented over the prime field" );
    assert_eq!(parity(&element_test2), true);
    assert_eq!(parity(&element_test3), false);
    assert_eq!(parity(&element_test4), true);
}

#[test]
fn test_parity_of_cubic_extension_elements() {
    let a1 = Fq2::new(Fq::from(0), Fq::from(0));
    let a2 = Fq2::new(Fq::from(0), Fq::from(1));
    let a3 = Fq2::new(Fq::from(1), Fq::from(0));
    let a4 = Fq2::new(Fq::from(1), Fq::from(1));
    let a5 = Fq2::new(Fq::from(0), Fq::from(2));

    let element_test1 = Fq6::new(a1, a2, a3);
    let element_test2 = Fq6::new(a2, a3, a4);
    let element_test3 = Fq6::new(a3, a4, a1);
    let element_test4 = Fq6::new(a4, a1, a2);
    let element_test5 = Fq6::new(a1, a5, a2);

    assert_eq!(parity(&element_test1), true, "parity is the oddness of first non-zero coefficient of element represented over the prime field");
    assert_eq!(parity(&element_test2), true, "parity is the oddness of first non-zero coefficient of element represented over the prime field");
    assert_eq!(parity(&element_test3), true);
    assert_eq!(parity(&element_test4), true);
    assert_eq!(parity(&element_test5), false);
}
