use crate::*;
use ark_algebra_test_templates::*;

test_field!(100; fr; Fr; mont_prime_field);
test_field!(100; fq; Fq; mont_prime_field);
test_field!(100; fq3; Fq3);
test_field!(100; fq6; Fq6);
