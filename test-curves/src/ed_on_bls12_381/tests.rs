use crate::ed_on_bls12_381::*;
use ark_algebra_test_templates::*;

test_field!(fr; Fr; mont_prime_field);
test_field!(fq; Fq; mont_prime_field);
test_group!(g; Projective; te);
