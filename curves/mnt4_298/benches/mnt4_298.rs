use ark_algebra_bench_templates::*;
use ark_mnt4_298::{
    fq::Fq, fq2::Fq2, fr::Fr, Fq4, G1Projective as G1, G2Projective as G2, MNT4_298,
};

bench!(
    Name = "MNT4_298",
    Pairing = MNT4_298,
    G1 = G1,
    G2 = G2,
    ScalarField = Fr,
    G1BaseField = Fq,
    G2BaseField = Fq2,
    TargetField = Fq4,
);
