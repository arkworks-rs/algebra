use ark_algebra_bench_templates::*;
use ark_vesta::{fq::Fq, fr::Fr, Projective as G};

bench!(
    Name = "Vesta",
    Group = G,
    ScalarField = Fr,
    PrimeBaseField = Fq,
);
