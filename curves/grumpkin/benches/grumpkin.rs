use ark_algebra_bench_templates::*;
use ark_grumpkin::{fq::Fq, fr::Fr, Projective as G};

bench!(
    Name = "Grumpkin",
    Group = G,
    ScalarField = Fr,
    PrimeBaseField = Fq,
);
