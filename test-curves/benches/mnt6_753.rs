use ark_algebra_bench_templates::*;
use ark_test_curves::mnt6_753::{fq::Fq, fq3::Fq3, fr::Fr};

f_bench!(prime, "MNT6_753", Fq);
f_bench!(prime, "MNT6_753", Fr);
f_bench!(extension, "MNT6_753", Fq3);

criterion_main!(fq::benches, fr::benches, fq3::benches);
