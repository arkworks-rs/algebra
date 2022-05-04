use crate::hashing::HashToCurve;
use crate::{
    hashing::{
        curve_maps::swu::{parity, SWUMap, SWUParams},
        field_hashers::DefaultFieldHasher,
        map_to_curve_hasher::{MapToCurve, MapToCurveBasedHasher},
    },
    models::SWModelParameters,
    short_weierstrass_jacobian::GroupAffine,
    ModelParameters,
};
use ark_ff::{fields::Fp64, MontBackend, MontFp};

use ark_ff::SquareRootField;
use ark_std::vec::Vec;
use ark_test_curves::bls12_381::{Fq, Fq2, Fq6};
use hashbrown::HashMap;

#[cfg(all(test, feature = "std"))]
mod json;
#[cfg(all(test, feature = "std"))]
mod suites;

#[derive(ark_ff::MontConfig)]
#[modulus = "127"]
#[generator = "6"]
pub struct F127Config;
pub type F127 = Fp64<MontBackend<F127Config, 1>>;

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
    use sha2::Sha256;

    let test_swu_to_curve_hasher = MapToCurveBasedHasher::<
        GroupAffine<TestSWUMapToCurveParams>,
        DefaultFieldHasher<Sha256, 128>,
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
