use crate::*;
use ark_algebra_test_templates::*;

test_field!(100; fr; Fr; mont_prime_field);
test_field!(100; fq; Fq; mont_prime_field);
test_field!(100; fq2; Fq2);
test_field!(100; fq4; Fq4);
