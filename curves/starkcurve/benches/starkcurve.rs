use ark_algebra_bench_templates::*;
use ark_starkcurve::{fq::Fq, fr::Fr, Projective as G};

bench!(
    Name = "StarkCurve",
    Group = G,
    ScalarField = Fr,
    PrimeBaseField = Fq,
);
