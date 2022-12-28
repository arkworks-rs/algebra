extern crate criterion;
mod common;

use ark_ff::FftField;
use ark_poly::{
    polynomial::{univariate::DensePolynomial, DenseUVPolynomial},
    EvaluationDomain, MixedRadixEvaluationDomain, Radix2EvaluationDomain,
};
use ark_test_curves::{bls12_381::Fr as bls12_381_fr, mnt4_753::Fq as mnt6_753_fr};
use common::size_range;
use criterion::{criterion_group, criterion_main, Bencher, BenchmarkId, Criterion};

// degree bounds to benchmark on
// e.g. degree bound of 2^{15}, means we do an FFT for a degree (2^{15} - 1) polynomial
const BENCHMARK_MIN_DEGREE: usize = 1 << 15;
const BENCHMARK_MAX_DEGREE_BLS12_381: usize = 1 << 22;
const BENCHMARK_MAX_DEGREE_MNT6_753: usize = 1 << 17;
const BENCHMARK_LOG_INTERVAL_DEGREE: usize = 1;

const ENABLE_RADIX2_BENCHES: bool = true;
const ENABLE_MIXED_RADIX_BENCHES: bool = true;

// returns vec![2^{min}, 2^{min + interval}, ..., 2^{max}], where:
// interval = BENCHMARK_LOG_INTERVAL_DEGREE
// min      = ceil(log_2(BENCHMARK_MIN_DEGREE))
// max      = ceil(log_2(BENCHMARK_MAX_DEGREE))
fn default_size_range_bls12_381() -> Vec<usize> {
    size_range(
        BENCHMARK_LOG_INTERVAL_DEGREE,
        BENCHMARK_MIN_DEGREE,
        BENCHMARK_MAX_DEGREE_BLS12_381,
    )
}

fn default_size_range_mnt6_753() -> Vec<usize> {
    size_range(
        BENCHMARK_LOG_INTERVAL_DEGREE,
        BENCHMARK_MIN_DEGREE,
        BENCHMARK_MAX_DEGREE_MNT6_753,
    )
}

fn setup_bench(
    c: &mut Criterion,
    name: &str,
    bench_fn: fn(&mut Bencher, &usize),
    size_range: &[usize],
) {
    let mut group = c.benchmark_group(name);
    for degree in size_range.iter() {
        group.bench_with_input(BenchmarkId::from_parameter(degree), degree, bench_fn);
    }
    group.finish();
}

fn fft_setup<F: FftField, D: EvaluationDomain<F>>(degree: usize) -> (D, Vec<F>) {
    fft_setup_with_domain_size(degree, degree)
}

fn fft_setup_with_domain_size<F: FftField, D: EvaluationDomain<F>>(
    degree: usize,
    domain_size: usize,
) -> (D, Vec<F>) {
    let mut rng = &mut ark_std::test_rng();
    let domain = D::new(domain_size).unwrap();
    let a = DensePolynomial::<F>::rand(degree - 1, &mut rng)
        .coeffs()
        .to_vec();
    (domain, a)
}

fn bench_fft_in_place<F: FftField, D: EvaluationDomain<F>>(b: &mut Bencher, degree: &usize) {
    // Per benchmark setup
    let (domain, mut a) = fft_setup::<F, D>(*degree);
    b.iter(|| {
        // Per benchmark iteration
        domain.fft_in_place(&mut a);
    });
}

fn bench_large_domain_fft_in_place<F: FftField, D: EvaluationDomain<F>>(
    b: &mut Bencher,
    degree: &usize,
) {
    // Per benchmark setup
    let (domain, mut a) = fft_setup_with_domain_size::<F, D>(*degree, degree << 2);
    b.iter(|| {
        // Per benchmark iteration
        domain.fft_in_place(&mut a);
    });
}

fn bench_ifft_in_place<F: FftField, D: EvaluationDomain<F>>(b: &mut Bencher, degree: &usize) {
    // Per benchmark setup
    let (domain, mut a) = fft_setup::<F, D>(*degree);
    b.iter(|| {
        // Per benchmark iteration
        domain.ifft_in_place(&mut a);
    });
}

fn bench_coset_fft_in_place<F: FftField, D: EvaluationDomain<F>>(b: &mut Bencher, degree: &usize) {
    // Per benchmark setup
    let (domain, mut a) = fft_setup::<F, D>(*degree);
    let coset_domain = domain.get_coset(F::GENERATOR).unwrap();
    b.iter(|| {
        // Per benchmark iteration
        coset_domain.fft_in_place(&mut a);
    });
}

fn bench_coset_ifft_in_place<F: FftField, D: EvaluationDomain<F>>(b: &mut Bencher, degree: &usize) {
    // Per benchmark setup
    let (domain, mut a) = fft_setup::<F, D>(*degree);
    let coset_domain = domain.get_coset(F::GENERATOR).unwrap();
    b.iter(|| {
        // Per benchmark iteration
        coset_domain.ifft_in_place(&mut a);
    });
}

fn fft_benches<F: FftField, D: EvaluationDomain<F>>(
    c: &mut Criterion,
    name: &'static str,
    size_range: &[usize],
) {
    let bench_name = format!("{name} - Subgroup FFT");
    setup_bench(c, &bench_name, bench_fft_in_place::<F, D>, size_range);
    let bench_name = format!("{name} - Subgroup FFT on larger domain");
    setup_bench(
        c,
        &bench_name,
        bench_large_domain_fft_in_place::<F, D>,
        size_range,
    );
    let bench_name = format!("{name} - Subgroup IFFT");
    setup_bench(c, &bench_name, bench_ifft_in_place::<F, D>, size_range);
    let bench_name = format!("{name} - Coset FFT");
    setup_bench(c, &bench_name, bench_coset_fft_in_place::<F, D>, size_range);
    let bench_name = format!("{name} - Coset IFFT");
    setup_bench(
        c,
        &bench_name,
        bench_coset_ifft_in_place::<F, D>,
        size_range,
    );
}

fn bench_bls12_381(c: &mut Criterion) {
    let name = "BLS12_381 - Radix2";
    if ENABLE_RADIX2_BENCHES {
        fft_benches::<bls12_381_fr, Radix2EvaluationDomain<bls12_381_fr>>(
            c,
            name,
            &default_size_range_bls12_381(),
        );
    }
}

fn bench_mnt6_753(c: &mut Criterion) {
    let name = "MNT6_753 - Mixed Radix";
    if ENABLE_MIXED_RADIX_BENCHES {
        fft_benches::<mnt6_753_fr, MixedRadixEvaluationDomain<mnt6_753_fr>>(
            c,
            name,
            &default_size_range_mnt6_753(),
        );
    }
}

criterion_group!(benches, bench_bls12_381, bench_mnt6_753);
criterion_main!(benches);
