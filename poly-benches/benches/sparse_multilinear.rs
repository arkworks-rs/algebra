//! Benchmark for sparse multilinear polynomial
#[macro_use]
extern crate criterion;

use ark_poly::polynomial::multivariate::SparseMultilinearPolynomial;
use ark_poly::Polynomial;
use ark_std::ops::Range;
use ark_std::{test_rng, UniformRand};
use ark_test_curves::bls12_381;
use criterion::{black_box, BenchmarkId, Criterion};

type Fr = bls12_381::Fr;

const NUM_VARIABLES_RANGE: Range<usize> = 12..23;

fn arithmetic_op_bench(c: &mut Criterion) {
    let mut rng = test_rng();

    let mut group = c.benchmark_group("Add");
    for nv in NUM_VARIABLES_RANGE {
        let num_nonzero_entries = 1 << (nv / 2);
        group.bench_with_input(
            BenchmarkId::new("add", num_nonzero_entries),
            &num_nonzero_entries,
            |b, &num_nonzero_entries| {
                let poly1 = SparseMultilinearPolynomial::<Fr>::rand_with_config(
                    nv,
                    num_nonzero_entries,
                    &mut rng,
                );
                let poly2 = SparseMultilinearPolynomial::<Fr>::rand_with_config(
                    nv,
                    num_nonzero_entries,
                    &mut rng,
                );
                b.iter(|| black_box(&poly1 + &poly2))
            },
        );
    }
    group.finish();

    let mut group = c.benchmark_group("Sub");
    for nv in NUM_VARIABLES_RANGE {
        let num_nonzero_entries = 1 << (nv / 2);
        group.bench_with_input(
            BenchmarkId::new("sub", num_nonzero_entries),
            &num_nonzero_entries,
            |b, &num_nonzero_entries| {
                let poly1 = SparseMultilinearPolynomial::<Fr>::rand_with_config(
                    nv,
                    num_nonzero_entries,
                    &mut rng,
                );
                let poly2 = SparseMultilinearPolynomial::<Fr>::rand_with_config(
                    nv,
                    num_nonzero_entries,
                    &mut rng,
                );
                b.iter(|| black_box(&poly1 - &poly2))
            },
        );
    }
    group.finish();
}

fn evaluation_op_bench(c: &mut Criterion) {
    let mut rng = test_rng();
    let mut group = c.benchmark_group("Evaluate");
    for nv in NUM_VARIABLES_RANGE {
        let num_nonzero_entries = 1 << (nv / 2);
        group.bench_with_input(
            BenchmarkId::new("evaluate", num_nonzero_entries),
            &num_nonzero_entries,
            |b, &num_nonzero_entries| {
                let poly = SparseMultilinearPolynomial::<Fr>::rand_with_config(
                    nv,
                    num_nonzero_entries,
                    &mut rng,
                );
                let point = (0..nv).map(|_| Fr::rand(&mut rng)).collect();
                b.iter(|| black_box(poly.evaluate(&point)))
            },
        );
    }
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default().significance_level(0.1).sample_size(100);
    targets = arithmetic_op_bench, evaluation_op_bench
}
criterion_main!(benches);
