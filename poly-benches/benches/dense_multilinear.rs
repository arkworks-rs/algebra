#[macro_use]
extern crate criterion;

use ark_ff::Field;
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_std::{ops::Range, test_rng};
use ark_test_curves::bls12_381;
use criterion::{black_box, BenchmarkId, Criterion};

const NUM_VARIABLES_RANGE: Range<usize> = 10..21;

fn arithmetic_op_bench<F: Field>(c: &mut Criterion) {
    let mut rng = test_rng();

    let mut group = c.benchmark_group("DenseMultilinear::Add");
    for nv in NUM_VARIABLES_RANGE {
        group.bench_with_input(BenchmarkId::from_parameter(nv), &nv, |b, &nv| {
            let poly1 = DenseMultilinearExtension::<F>::rand(nv, &mut rng);
            let poly2 = DenseMultilinearExtension::<F>::rand(nv, &mut rng);
            b.iter(|| black_box(&poly1 + &poly2))
        });
    }
    group.finish();

    let mut group = c.benchmark_group("DenseMultilinear::Sub");
    for nv in NUM_VARIABLES_RANGE {
        group.bench_with_input(BenchmarkId::from_parameter(nv), &nv, |b, &nv| {
            let poly1 = DenseMultilinearExtension::<F>::rand(nv, &mut rng);
            let poly2 = DenseMultilinearExtension::<F>::rand(nv, &mut rng);
            b.iter(|| black_box(&poly1 - &poly2))
        });
    }
    group.finish();
}

fn evaluation_op_bench<F: Field>(c: &mut Criterion) {
    let mut rng = test_rng();
    let mut group = c.benchmark_group("DenseMultilinear::Evaluate");
    for nv in NUM_VARIABLES_RANGE {
        group.bench_with_input(BenchmarkId::from_parameter(nv), &nv, |b, &nv| {
            let poly = DenseMultilinearExtension::<F>::rand(nv, &mut rng);
            let point: Vec<_> = (0..nv).map(|_| F::rand(&mut rng)).collect();
            b.iter(|| black_box(poly.evaluate(&point).unwrap()))
        });
    }
    group.finish();
}

fn bench_bls_381(c: &mut Criterion) {
    arithmetic_op_bench::<bls12_381::Fr>(c);
    evaluation_op_bench::<bls12_381::Fr>(c);
}

criterion_group!(benches, bench_bls_381);
criterion_main!(benches);
