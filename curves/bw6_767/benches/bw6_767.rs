use ark_algebra_bench_templates::*;

use ark_bw6_767::{
    fq::Fq, fq3::Fq3, fq6::Fq6, fr::Fr, g1::G1Projective as G1, g2::G2Projective as G2, BW6_767,
};

bench!(
    Name = "BW6_767",
    Pairing = BW6_767,
    G1 = G1,
    G2 = G2,
    ScalarField = Fr,
    G1BaseField = Fq,
    G2BaseField = Fq3,
    TargetField = Fq6,
);
