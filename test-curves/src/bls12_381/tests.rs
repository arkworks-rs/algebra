#![allow(clippy::ptr_arg)]
use crate::bls12_381::*;
use ark_algebra_test_templates::*;

test_field!(fr; Fr; mont_prime_field);
#[cfg(feature = "bls12_381_curve")]
test_field!(fq; Fq; mont_prime_field);
#[cfg(feature = "bls12_381_curve")]
test_field!(fq2; Fq2);
#[cfg(feature = "bls12_381_curve")]
test_field!(fq6; Fq6);
#[cfg(feature = "bls12_381_curve")]
test_field!(fq12; Fq12);
#[cfg(feature = "bls12_381_curve")]
test_group!(g1; G1Projective; sw);
#[cfg(feature = "bls12_381_curve")]
test_group!(g2; G2Projective; sw);
#[cfg(feature = "bls12_381_curve")]
test_group!(pairing_output; ark_ec::pairing::PairingOutput<Bls12_381>; msm);
#[cfg(feature = "bls12_381_curve")]
test_group!(glv; G1Projective; glv);
#[cfg(feature = "bls12_381_curve")]
test_pairing!(pairing; crate::bls12_381::Bls12_381);
#[cfg(feature = "bls12_381_curve")]
test_h2c!(g1_h2c; "./src/testdata"; "BLS12381G1"; crate::bls12_381::g1::Config; crate::bls12_381::Fq; crate::bls12_381::Fq; 1);
#[cfg(feature = "bls12_381_curve")]
test_h2c!(g2_hc2; "./src/testdata"; "BLS12381G2"; crate::bls12_381::g2::Config; crate::bls12_381::Fq2; crate::bls12_381::Fq; 2);

#[cfg(feature = "bls12_381_curve")]
#[test]
fn test_g2_prepared_rejects_wrong_number_of_coefficients() {
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::{test_rng, vec, UniformRand};

    let mut rng = test_rng();
    let q = G2Projective::rand(&mut rng).into_affine();
    let prepared = G2Prepared::from(q);

    let mut bytes = vec![];
    prepared.serialize_compressed(&mut bytes).unwrap();
    let decoded = G2Prepared::deserialize_compressed(&bytes[..]).expect("valid encoding");
    assert_eq!(decoded, prepared);

    let mut truncated = prepared.clone();
    truncated.ell_coeffs.pop();
    bytes.clear();
    truncated.serialize_compressed(&mut bytes).unwrap();
    assert!(G2Prepared::deserialize_compressed(&bytes[..]).is_err());
    assert!(G2Prepared::deserialize_compressed_unchecked(&bytes[..]).is_ok());

    let mut extra = prepared.clone();
    extra.ell_coeffs.push(extra.ell_coeffs[0]);
    bytes.clear();
    extra.serialize_compressed(&mut bytes).unwrap();
    assert!(G2Prepared::deserialize_compressed(&bytes[..]).is_err());

    let infinity = G2Prepared::from(G2Affine::zero());
    bytes.clear();
    infinity.serialize_compressed(&mut bytes).unwrap();
    assert!(G2Prepared::deserialize_compressed(&bytes[..]).is_ok());
    let mut bad_infinity = infinity.clone();
    bad_infinity.ell_coeffs.push(prepared.ell_coeffs[0]);
    bytes.clear();
    bad_infinity.serialize_compressed(&mut bytes).unwrap();
    assert!(G2Prepared::deserialize_compressed(&bytes[..]).is_err());
}
