use ark_algebra_bench_templates::*;
use ark_test_curves::mnt4_753::{fq::Fq, fr::Fr, G1Projective as G1};

bench!(
    Name = "MNT4_753",
    Group = G1,
    ScalarField = Fr,
    BaseField = Fq,
);
