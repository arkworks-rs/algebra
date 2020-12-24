//! Benchmark for dense multilinear polynomial
#[macro_use]
extern crate criterion;

use ark_poly::polynomial::multivariate::DenseMultilinearPolynomial;
use ark_poly::{MVPolynomial, Polynomial};
use ark_std::ops::Range;
use ark_std::{test_rng, UniformRand};
use ark_test_curves::bls12_381;
use criterion::{black_box, BenchmarkId, Criterion};

type Fr = bls12_381::Fr;

const NUM_VARIABLES_RANGE: Range<usize> = 10..21;

fn arithmetic_op_bench(c: &mut Criterion) {
    let mut rng = test_rng();

    let mut group = c.benchmark_group("Add");
    for nv in NUM_VARIABLES_RANGE {
        group.bench_with_input(BenchmarkId::new("Add", nv), &nv, |b, &nv| {
            let poly1 = DenseMultilinearPolynomial::<Fr>::rand(nv, nv, &mut rng);
            let poly2 = DenseMultilinearPolynomial::<Fr>::rand(nv, nv, &mut rng);
            b.iter(|| black_box(&poly1 + &poly2))
        });
    }
    group.finish();

    let mut group = c.benchmark_group("Sub");
    for nv in NUM_VARIABLES_RANGE {
        group.bench_with_input(BenchmarkId::new("Sub", nv), &nv, |b, &nv| {
            let poly1 = DenseMultilinearPolynomial::<Fr>::rand(nv, nv, &mut rng);
            let poly2 = DenseMultilinearPolynomial::<Fr>::rand(nv, nv, &mut rng);
            b.iter(|| black_box(&poly1 - &poly2))
        });
    }
    group.finish();
}

fn evaluation_op_bench(c: &mut Criterion) {
    let mut rng = test_rng();
    let mut group = c.benchmark_group("Evaluate");
    for nv in NUM_VARIABLES_RANGE {
        group.bench_with_input(BenchmarkId::new("evaluate", nv), &nv, |b, &nv| {
            let poly = DenseMultilinearPolynomial::<Fr>::rand(nv, nv, &mut rng);
            let point = (0..nv).map(|_| Fr::rand(&mut rng)).collect();
            b.iter(|| black_box(poly.evaluate(&point)))
        });
    }
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default().significance_level(0.1).sample_size(100);
    targets = arithmetic_op_bench, evaluation_op_bench
}
criterion_main!(benches);
