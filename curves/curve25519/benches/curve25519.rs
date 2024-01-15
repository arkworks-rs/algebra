use ark_algebra_bench_templates::*;
use ark_curve25519::{EdwardsProjective as G, Fq, Fr};

bench!(
    Name = "Curve25519",
    Group = G,
    ScalarField = Fr,
    PrimeBaseField = Fq,
);
