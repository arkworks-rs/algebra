#[macro_use]
extern crate criterion;

use ark_ff::Field;
use ark_poly::{MultilinearExtension, SparseMultilinearExtension};
use ark_std::{ops::Range, test_rng};
use ark_test_curves::bls12_381;
use criterion::{black_box, BenchmarkId, Criterion};

const NUM_VARIABLES_RANGE: Range<usize> = 12..23;

fn arithmetic_op_bench<F: Field>(c: &mut Criterion) {
    let mut rng = test_rng();

    let mut group = c.benchmark_group("SparseMultilinear");
    for nv in NUM_VARIABLES_RANGE {
        let num_nonzero_entries = 1 << (dbg!(nv) / 2);
        group.bench_with_input(
            BenchmarkId::new(format!("Add with num_vars = {nv}"), num_nonzero_entries),
            &num_nonzero_entries,
            |b, &num_nonzero_entries| {
                let poly1 = SparseMultilinearExtension::<F>::rand_with_config(
                    nv,
                    num_nonzero_entries,
                    &mut rng,
                );
                let poly2 = SparseMultilinearExtension::<F>::rand_with_config(
                    nv,
                    num_nonzero_entries,
                    &mut rng,
                );
                b.iter(|| black_box(&poly1 + &poly2))
            },
        );
    }

    for nv in NUM_VARIABLES_RANGE {
        let num_nonzero_entries = 1 << (nv / 2);
        group.bench_with_input(
            BenchmarkId::new(format!("Sub with num_vars = {nv}"), num_nonzero_entries),
            &num_nonzero_entries,
            |b, &num_nonzero_entries| {
                let poly1 = SparseMultilinearExtension::<F>::rand_with_config(
                    nv,
                    num_nonzero_entries,
                    &mut rng,
                );
                let poly2 = SparseMultilinearExtension::<F>::rand_with_config(
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

fn evaluation_op_bench<F: Field>(c: &mut Criterion) {
    let mut rng = test_rng();
    let mut group = c.benchmark_group("SparseMultilinear");
    for nv in NUM_VARIABLES_RANGE {
        let num_nonzero_entries = 1 << (nv / 2);
        group.bench_with_input(
            BenchmarkId::new(format!("Eval with num_vars = {nv}"), num_nonzero_entries),
            &num_nonzero_entries,
            |b, &num_nonzero_entries| {
                let poly = SparseMultilinearExtension::<F>::rand_with_config(
                    nv,
                    num_nonzero_entries,
                    &mut rng,
                );
                let point: Vec<_> = (0..nv).map(|_| F::rand(&mut rng)).collect();
                b.iter(|| black_box(poly.evaluate(&point).unwrap()))
            },
        );
    }
    group.finish();
}

fn bench_bls381(c: &mut Criterion) {
    arithmetic_op_bench::<bls12_381::Fr>(c);
    evaluation_op_bench::<bls12_381::Fr>(c);
}

criterion_group!(benches, bench_bls381);
criterion_main!(benches);
