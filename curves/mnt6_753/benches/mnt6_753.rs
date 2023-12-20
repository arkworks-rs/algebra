use ark_algebra_bench_templates::*;
use ark_mnt6_753::{
    fq::Fq, fq3::Fq3, fr::Fr, Fq6, G1Projective as G1, G2Projective as G2, MNT6_753,
};

bench!(
    Name = "MNT6_753",
    Pairing = MNT6_753,
    G1 = G1,
    G2 = G2,
    ScalarField = Fr,
    G1BaseField = Fq,
    G2BaseField = Fq3,
    TargetField = Fq6,
);
