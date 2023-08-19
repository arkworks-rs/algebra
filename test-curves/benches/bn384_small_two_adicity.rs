use ark_algebra_bench_templates::{bench, criterion_main, field_common, paste, prime_field, sqrt};
use ark_test_curves::bn384_small_two_adicity::{fq::Fq, fr::Fr, G1Projective as G1};

bench!(Name = "BN384", Group = G1, ScalarField = Fr, BaseField = Fq,);
