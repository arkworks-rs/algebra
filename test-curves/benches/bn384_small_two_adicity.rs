use ark_algebra_bench_templates::{field_common, prime_field, sqrt};
use ark_ec_bench_templates::{bench, criterion_main, paste};
use ark_test_curves::bn384_small_two_adicity::{Fq, Fr, G1Projective as G1};

bench!(Name = "BN384", Group = G1, ScalarField = Fr, BaseField = Fq,);
