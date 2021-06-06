extern crate criterion;

use ark_ff::Field;
use ark_poly::{
    polynomial::univariate::DensePolynomial, polynomial::univariate::SparsePolynomial, Polynomial,
    UVPolynomial,
};
use ark_poly_benches::size_range;
use ark_std::rand::Rng;
use ark_test_curves::bls12_381::Fr as bls12_381_fr;
use criterion::BenchmarkId;
use criterion::{criterion_group, criterion_main, Bencher, Criterion};

const BENCHMARK_MIN_DEGREE: usize = 1 << 15;
const BENCHMARK_MAX_DEGREE: usize = 1 << 17;
const BENCHMARK_LOG_INTERVAL_DEGREE: usize = 1;

const ENABLE_ADD_BENCH: bool = true;
const ENABLE_ADD_ASSIGN_BENCH: bool = true;
const ENABLE_EVALUATE_BENCH: bool = true;
const ENABLE_SPARSE_EVALUATE_BENCH: bool = true;

// returns vec![2^{min}, 2^{min + interval}, ..., 2^{max}], where:
// interval = BENCHMARK_LOG_INTERVAL_DEGREE
// min      = ceil(log_2(BENCHMARK_MIN_DEGREE))
// max      = ceil(log_2(BENCHMARK_MAX_DEGREE))
fn default_size_range() -> Vec<usize> {
    size_range(
        BENCHMARK_LOG_INTERVAL_DEGREE,
        BENCHMARK_MIN_DEGREE,
        BENCHMARK_MAX_DEGREE,
    )
}

fn setup_bench<F: Field>(c: &mut Criterion, name: &str, bench_fn: fn(&mut Bencher, &usize)) {
    let mut group = c.benchmark_group(name);
    for degree in default_size_range().iter() {
        group.bench_with_input(BenchmarkId::from_parameter(degree), degree, bench_fn);
    }
    group.finish();
}

fn bench_sparse_poly_evaluate<F: Field>(b: &mut Bencher, non_zero_entries: &usize) {
    const MAX_DEGREE: usize = 1 << 15;
    // Per benchmark setup
    let mut rng = &mut ark_std::test_rng();
    let mut inner: Vec<(usize, F)> = Vec::with_capacity(*non_zero_entries);
    (0..*non_zero_entries)
        .for_each(|_| inner.push((rng.gen_range(0..MAX_DEGREE), F::rand(&mut rng))));
    let poly = SparsePolynomial::<F>::from_coefficients_vec(inner);
    b.iter(|| {
        // Per benchmark iteration
        let pt = F::rand(&mut rng);
        poly.evaluate(&pt);
    });
}

fn bench_poly_evaluate<F: Field>(b: &mut Bencher, degree: &usize) {
    // Per benchmark setup
    let mut rng = &mut ark_std::test_rng();
    let poly = DensePolynomial::<F>::rand(*degree, &mut rng);
    b.iter(|| {
        // Per benchmark iteration
        let pt = F::rand(&mut rng);
        poly.evaluate(&pt);
    });
}

fn bench_poly_add<F: Field>(b: &mut Bencher, degree: &usize) {
    // Per benchmark setup
    let mut rng = &mut ark_std::test_rng();
    let poly_one = DensePolynomial::<F>::rand(*degree, &mut rng);
    let poly_two = DensePolynomial::<F>::rand(*degree, &mut rng);
    b.iter(|| {
        // Per benchmark iteration
        let _poly_three = &poly_one + &poly_two;
    });
}

fn bench_poly_add_assign<F: Field>(b: &mut Bencher, degree: &usize) {
    // Per benchmark setup
    let mut rng = &mut ark_std::test_rng();
    let mut poly_one = DensePolynomial::<F>::rand(*degree, &mut rng);
    let poly_two = DensePolynomial::<F>::rand(*degree, &mut rng);
    b.iter(|| {
        // Per benchmark iteration
        poly_one += &poly_two;
    });
}

fn poly_benches<F: Field>(c: &mut Criterion, name: &'static str) {
    if ENABLE_ADD_BENCH {
        let cur_name = format!("{:?} - add_polynomial", name.clone());
        setup_bench::<F>(c, &cur_name, bench_poly_add::<F>);
    }
    if ENABLE_ADD_ASSIGN_BENCH {
        let cur_name = format!("{:?} - add_assign_polynomial", name.clone());
        setup_bench::<F>(c, &cur_name, bench_poly_add_assign::<F>);
    }
    if ENABLE_EVALUATE_BENCH {
        let cur_name = format!("{:?} - evaluate_polynomial", name.clone());
        setup_bench::<F>(c, &cur_name, bench_poly_evaluate::<F>);
    }
    if ENABLE_SPARSE_EVALUATE_BENCH {
        let cur_name = format!("{:?} - evaluate_sparse_polynomial", name.clone());
        setup_bench::<F>(c, &cur_name, bench_sparse_poly_evaluate::<F>);
    }
}

fn bench_bls12_381(c: &mut Criterion) {
    let name = "bls12_381";
    poly_benches::<bls12_381_fr>(c, name);
}

criterion_group!(benches, bench_bls12_381);
criterion_main!(benches);
