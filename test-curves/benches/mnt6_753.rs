use ark_algebra_bench_templates::*;
use ark_test_curves::mnt6_753::{fq::Fq, fq3::Fq3, fr::Fr};

f_bench!(prime, Fq, fq);
f_bench!(prime, Fr, fr);
f_bench!(extension, Fq3, fq3);

criterion_main!(fq::benches, fr::benches, fq3::benches);
