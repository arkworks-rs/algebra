use ark_ff::{FftField, UniformRand};
use ark_poly::{
    polynomial::{univariate::DensePolynomial, DenseUVPolynomial},
    EvaluationDomain, Radix2EvaluationDomain,
};
use ark_test_curves::bls12_381::Fr as bls12_381_fr;
use criterion::{criterion_group, criterion_main, Bencher, BenchmarkId, Criterion};

// Benchmark sizes to test the take() optimization impact
const BENCHMARK_SIZES: &[usize] = &[1024, 2048, 4096, 8192, 16384, 32768];

fn setup_bench(
    c: &mut Criterion,
    name: &str,
    bench_fn: fn(&mut Bencher<'_>, &usize),
    sizes: &[usize],
) {
    let mut group = c.benchmark_group(name);
    for size in sizes {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, bench_fn);
    }
    group.finish();
}

fn fft_setup<F: FftField>(size: usize) -> (Radix2EvaluationDomain<F>, Vec<F>) {
    let mut rng = &mut ark_std::test_rng();
    let domain = Radix2EvaluationDomain::<F>::new(size).unwrap();
    let poly = DensePolynomial::rand(size - 1, &mut rng);
    let coeffs = poly.coeffs().to_vec();
    (domain, coeffs)
}

fn bench_fft_in_place(b: &mut Bencher<'_>, size: &usize) {
    let (domain, mut coeffs) = fft_setup::<bls12_381_fr>(*size);
    b.iter(|| {
        domain.fft_in_place(&mut coeffs);
    });
}

fn bench_ifft_in_place(b: &mut Bencher<'_>, size: &usize) {
    let (domain, mut coeffs) = fft_setup::<bls12_381_fr>(*size);
    b.iter(|| {
        domain.ifft_in_place(&mut coeffs);
    });
}

fn bench_coset_fft_in_place(b: &mut Bencher<'_>, size: &usize) {
    let (domain, mut coeffs) = fft_setup::<bls12_381_fr>(*size);
    let coset_domain = domain.get_coset(bls12_381_fr::GENERATOR).unwrap();
    b.iter(|| {
        coset_domain.fft_in_place(&mut coeffs);
    });
}

fn bench_coset_ifft_in_place(b: &mut Bencher<'_>, size: &usize) {
    let (domain, mut coeffs) = fft_setup::<bls12_381_fr>(*size);
    let coset_domain = domain.get_coset(bls12_381_fr::GENERATOR).unwrap();
    b.iter(|| {
        coset_domain.ifft_in_place(&mut coeffs);
    });
}

fn bench_lagrange_evaluation(b: &mut Bencher<'_>, size: &usize) {
    let (domain, _coeffs) = fft_setup::<bls12_381_fr>(*size);
    let mut rng = &mut ark_std::test_rng();
    let tau = bls12_381_fr::rand(&mut rng);
    
    b.iter(|| {
        domain.evaluate_all_lagrange_coefficients(tau);
    });
}

fn bench_polynomial_multiplication(b: &mut Bencher<'_>, size: &usize) {
    let mut rng = &mut ark_std::test_rng();
    let poly1: DensePolynomial<bls12_381_fr> = DensePolynomial::rand(*size - 1, &mut rng);
    let poly2: DensePolynomial<bls12_381_fr> = DensePolynomial::rand(*size - 1, &mut rng);
    
    b.iter(|| {
        let _result = &poly1 * &poly2;
    });
}

fn take_optimization_benches(c: &mut Criterion) {
    // FFT operations that benefit from take() optimization
    setup_bench(c, "FFT - Take Optimization", bench_fft_in_place, BENCHMARK_SIZES);
    setup_bench(c, "IFFT - Take Optimization", bench_ifft_in_place, BENCHMARK_SIZES);
    setup_bench(c, "Coset FFT - Take Optimization", bench_coset_fft_in_place, BENCHMARK_SIZES);
    setup_bench(c, "Coset IFFT - Take Optimization", bench_coset_ifft_in_place, BENCHMARK_SIZES);
    
    // Lagrange evaluation that benefits from take() optimization
    setup_bench(c, "Lagrange Evaluation - Take Optimization", bench_lagrange_evaluation, BENCHMARK_SIZES);
    
    // Polynomial operations
    setup_bench(c, "Polynomial Multiplication - Take Optimization", bench_polynomial_multiplication, BENCHMARK_SIZES);
}

criterion_group!(benches, take_optimization_benches);
criterion_main!(benches);
