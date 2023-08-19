use ark_algebra_bench_templates::{bench, criterion_main, field_common, paste, prime_field, sqrt};
use ark_test_curves::ed_on_bls12_381::{Fq, Fr, Projective};

bench!(
    Name = "EdOnBls12_381",
    Group = Projective,
    ScalarField = Fr,
    BaseField = Fq,
);
