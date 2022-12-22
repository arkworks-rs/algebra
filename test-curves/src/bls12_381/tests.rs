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
test_pairing!(pairing; crate::bls12_381::Bls12_381);
#[cfg(feature = "bls12_381_curve")]
test_h2c!(g1_h2c; "./src/testdata"; "BLS12381G1"; crate::bls12_381::g1::Config; crate::bls12_381::Fq; crate::bls12_381::Fq; 1);
#[cfg(feature = "bls12_381_curve")]
test_h2c!(g2_hc2; "./src/testdata"; "BLS12381G2"; crate::bls12_381::g2::Config; crate::bls12_381::Fq2; crate::bls12_381::Fq; 2);
