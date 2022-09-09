use ark_algebra_bench_templates::*;
use ark_test_curves::bn384_small_two_adicity::{fq::Fq, fr::Fr, G1Projective as G1};

mod g1 {
    use super::*;
    ec_bench!(G1);
}
f_bench!(prime, Fq, fq);
f_bench!(prime, Fr, fr);

criterion_main!(g1::benches, fq::benches, fr::benches);
