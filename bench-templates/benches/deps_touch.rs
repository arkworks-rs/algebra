use ark_ec as _;
use ark_std as _;
use criterion::{criterion_group, criterion_main, Criterion};

fn bench_deps(c: &mut Criterion) {
    let mut g = c.benchmark_group("deps_touch");
    let a: ark_ff::BigInt<1> = ark_ff::BigInt::from(123u64);
    let _ = a;
    let _ = ark_serialize::Compress::Yes;
    g.bench_function("noop", |b| b.iter(|| ()));
    g.finish();
}

criterion_group!(benches, bench_deps);
criterion_main!(benches);
