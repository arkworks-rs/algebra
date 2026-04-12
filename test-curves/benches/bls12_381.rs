use ark_algebra_bench_templates::{field_common, prime_field, sqrt};
use ark_ec_bench_templates::{bench, criterion_main, paste};
use ark_test_curves::bls12_381::{
    Bls12_381, Fq, Fq12, Fq2, Fr, G1Projective as G1, G2Projective as G2,
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
