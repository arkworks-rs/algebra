use rand;

extern crate criterion;

use ark_ff::Field;
use ark_poly::{polynomial::univariate::DensePolynomial, Polynomial, UVPolynomial};
use ark_test_curves::bls12_381::Fr as bls12_381_fr;
use criterion::BenchmarkId;
use criterion::Criterion;
use criterion::{criterion_group, criterion_main};

const POLY_LOG_MIN_SIZE: usize = 15;
const POLY_EVALUATE_MAX_DEGREE: usize = 1 << 17;

// returns vec![2^{POLY_LOG_MIN_SIZE}, ... 2^n], where n = ceil(log_2(max_degree))
fn size_range(max_degree: usize) -> Vec<usize> {
    let mut to_ret = vec![1 << POLY_LOG_MIN_SIZE];
    while *to_ret.last().unwrap() < max_degree {
        to_ret.push(to_ret.last().unwrap() * 2);
    }
    to_ret
}

fn bench_poly_evaluate<F: Field>(c: &mut Criterion, name: &'static str) {
    let mut group = c.benchmark_group(format!("{:?} - evaluate_polynomial", name));
    for degree in size_range(POLY_EVALUATE_MAX_DEGREE).iter() {
        group.bench_with_input(BenchmarkId::from_parameter(degree), degree, |b, &degree| {
            // Per benchmark setup
            let mut rng = &mut rand::thread_rng();
            let poly = DensePolynomial::<F>::rand(degree, &mut rng);
            b.iter(|| {
                // Per benchmark iteration
                let pt = F::rand(&mut rng);
                poly.evaluate(&pt);
            });
        });
    }
    group.finish();
}

fn bench_bls12_381(c: &mut Criterion) {
    let name = "bls12_381";
    bench_poly_evaluate::<bls12_381_fr>(c, name);
}

criterion_group!(benches, bench_bls12_381);
criterion_main!(benches);
