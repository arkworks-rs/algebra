use ark_algebra_bench_templates::{bench, criterion_main, field_common, paste, prime_field, sqrt};
use ark_test_curves::mnt4_753::{fq::Fq, fr::Fr, G1Projective as G1};

bench!(
    Name = "MNT4_753",
    Group = G1,
    ScalarField = Fr,
    BaseField = Fq,
);
