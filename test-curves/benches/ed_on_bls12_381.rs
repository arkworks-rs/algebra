use ark_algebra_bench_templates::*;
use ark_test_curves::ed_on_bls12_381::{Fq, Fr, Projective};

mod group {
    use super::*;
    ec_bench!(Projective);
}
f_bench!(prime, Fq, fq);
f_bench!(prime, Fr, fr);

criterion_main!(group::benches, fq::benches, fr::benches);
