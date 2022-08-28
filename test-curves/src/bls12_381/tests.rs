use crate::bls12_381::*;
use ark_algebra_test_templates::*;

test_field!(fr; Fr; mont_prime_field);
test_field!(fq; Fq; mont_prime_field);
test_field!(fq2; Fq2);
test_field!(fq6; Fq6);
test_field!(fq12; Fq12);
test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<Bls12_381>; msm);
test_pairing!(pairing; crate::bls12_381::Bls12_381);
