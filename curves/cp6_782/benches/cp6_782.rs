use ark_algebra_bench_templates::*;
use ark_cp6_782::{
    fq::Fq, fq3::Fq3, fq6::Fq6, fr::Fr, g1::G1Projective as G1, g2::G2Projective as G2, CP6_782,
};

bench!(
    Name = "CP6_782",
    Pairing = CP6_782,
    G1 = G1,
    G2 = G2,
    ScalarField = Fr,
    G1BaseField = Fq,
    G2BaseField = Fq3,
    TargetField = Fq6,
);
