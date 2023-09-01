use ark_algebra_bench_templates::{bench, criterion_main, field_common, paste, prime_field, sqrt};
use ark_test_curves::bls12_381::{
    fq::Fq, fq2::Fq2, fr::Fr, Bls12_381, Fq12, G1Projective as G1, G2Projective as G2,
};

bench!(
    Name = "Bls12_381",
    Pairing = Bls12_381,
    G1 = G1,
    G2 = G2,
    ScalarField = Fr,
    G1BaseField = Fq,
    G2BaseField = Fq2,
    TargetField = Fq12,
);
