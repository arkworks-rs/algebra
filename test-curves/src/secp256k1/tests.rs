use crate::secp256k1::{Fq, Fr, G1Projective};
use ark_algebra_test_templates::{test_field, test_group};

test_field!(fq; Fq; mont_prime_field);
test_field!(fr; Fr; mont_prime_field);
test_group!(g1; G1Projective);
