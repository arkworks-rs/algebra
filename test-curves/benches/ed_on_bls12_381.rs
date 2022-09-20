use ark_algebra_bench_templates::*;
use ark_test_curves::ed_on_bls12_381::{Fq, Fr, Projective};

bench!(
    Name = "EdOnBls12_381",
    Group = Projective,
    ScalarField = Fr,
    BaseField = Fq,
);
