use ark_algebra_bench_templates::{field_common, prime_field, sqrt};
use ark_ec_bench_templates::{bench, criterion_main, paste};
use ark_test_curves::ed_on_bls12_381::{Fq, Fr, Projective};

bench!(
    Name = "EdOnBls12_381",
    Group = Projective,
    ScalarField = Fr,
    BaseField = Fq,
);
