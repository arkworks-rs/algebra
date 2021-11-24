use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{BigInteger, Field, SquareRootField, UniformRand};
use criterion::{black_box, BenchmarkId, Criterion};

use std::iter;

#[allow(dead_code)]
pub fn field_arithmetic_bench<F: Field>(c: &mut Criterion, curve: &str, field: &str) {
    let mut rng = ark_std::test_rng();

    let mut group = c.benchmark_group("Add");

    let m: F = UniformRand::rand(&mut rng);
    let n: F = UniformRand::rand(&mut rng);
    group.bench_with_input(BenchmarkId::new(curve, field), &(&m, &n), |b, &(&m, &n)| {
        b.iter(|| black_box(m + n))
    });

    group.finish();

    let mut group = c.benchmark_group("Sub");

    let m: F = UniformRand::rand(&mut rng);
    let n: F = UniformRand::rand(&mut rng);
    group.bench_with_input(BenchmarkId::new(curve, field), &(&m, &n), |b, &(&m, &n)| {
        b.iter(|| black_box(m - n))
    });

    group.finish();

    let mut group = c.benchmark_group("Mul");

    let m: F = UniformRand::rand(&mut rng);
    let n: F = UniformRand::rand(&mut rng);
    group.bench_with_input(BenchmarkId::new(curve, field), &(&m, &n), |b, &(&m, &n)| {
        b.iter(|| black_box(m * n))
    });

    group.finish();

    let mut group = c.benchmark_group("Div");

    let m: F = UniformRand::rand(&mut rng);
    let n: F = UniformRand::rand(&mut rng);
    group.bench_with_input(BenchmarkId::new(curve, field), &(&m, &n), |b, &(&m, &n)| {
        b.iter(|| black_box(m / n))
    });

    group.finish();
}

#[allow(dead_code)]
pub fn curve_affine_arithmetic_bench<G: AffineCurve>(c: &mut Criterion, curve: &str, repr: &str) {
    let mut rng = ark_std::test_rng();

    let affine = iter::repeat(())
        .map(|_| UniformRand::rand(&mut rng))
        .take(100)
        .collect::<Vec<G>>();

    let mut group = c.benchmark_group("Sum(2)");

    group.bench_with_input(BenchmarkId::new(curve, repr), &affine[..2], |b, g| {
        b.iter(|| black_box(g.iter().sum::<G>()))
    });

    group.finish();

    let mut group = c.benchmark_group("Sum(10)");

    group.bench_with_input(BenchmarkId::new(curve, repr), &affine[..10], |b, g| {
        b.iter(|| black_box(g.iter().sum::<G>()))
    });

    group.finish();

    let mut group = c.benchmark_group("Sum(100)");

    group.bench_with_input(BenchmarkId::new(curve, repr), &affine[..100], |b, g| {
        b.iter(|| black_box(g.iter().sum::<G>()))
    });

    group.finish();
}

#[allow(dead_code)]
pub fn curve_projective_arithmetic_bench<G: ProjectiveCurve>(
    c: &mut Criterion,
    curve: &str,
    repr: &str,
) {
    let mut rng = ark_std::test_rng();

    let projective = iter::repeat(())
        .map(|_| UniformRand::rand(&mut rng))
        .take(100)
        .collect::<Vec<G>>();

    let mut group = c.benchmark_group("Add");

    group.bench_with_input(
        BenchmarkId::new(curve, repr),
        &(&projective[0], &projective[1]),
        |b, &(&m, &n)| b.iter(|| black_box(m + n)),
    );

    group.finish();

    let mut group = c.benchmark_group("Sub");

    group.bench_with_input(
        BenchmarkId::new(curve, repr),
        &(&projective[0], &projective[1]),
        |b, &(&m, &n)| b.iter(|| black_box(m - n)),
    );

    group.finish();

    let mut group = c.benchmark_group("MulScalar");

    let n: G::ScalarField = UniformRand::rand(&mut rng);
    group.bench_with_input(
        BenchmarkId::new(curve, repr),
        &(projective[0].clone(), &n),
        |b, &(mut m, &n)| b.iter(|| black_box(m *= n)),
    );

    group.finish();

    let mut group = c.benchmark_group("Double");

    group.bench_with_input(BenchmarkId::new(curve, repr), &projective[0], |b, m| {
        b.iter(|| black_box(m.double()))
    });

    group.finish();

    let mut group = c.benchmark_group("DoubleInPlace");

    group.bench_with_input(
        BenchmarkId::new(curve, repr),
        &(projective[0].clone()),
        |b, &(mut m)| {
            b.iter(|| {
                black_box(m.double_in_place());
            })
        },
    );

    group.finish();

    let mut group = c.benchmark_group("Sum(2)");

    group.bench_with_input(BenchmarkId::new(curve, repr), &projective[..2], |b, g| {
        b.iter(|| black_box(g.iter().sum::<G>()))
    });

    group.finish();

    let mut group = c.benchmark_group("Sum(10)");

    group.bench_with_input(BenchmarkId::new(curve, repr), &projective[..10], |b, g| {
        b.iter(|| black_box(g.iter().sum::<G>()))
    });

    group.finish();

    let mut group = c.benchmark_group("Sum(100)");

    group.bench_with_input(BenchmarkId::new(curve, repr), &projective[..100], |b, g| {
        b.iter(|| black_box(g.iter().sum::<G>()))
    });

    group.finish();
}

#[allow(dead_code)]
pub fn biginteger_bench<B: BigInteger>(c: &mut Criterion, repr: &str) {
    let mut rng = ark_std::test_rng();

    let mut group = c.benchmark_group("AddNoCarry");

    let m: B = UniformRand::rand(&mut rng);
    let n: B = UniformRand::rand(&mut rng);
    group.bench_with_input(repr, &(m, &n), |b, &(mut m, n)| {
        b.iter(|| black_box(m.add_nocarry(n)))
    });

    group.finish();

    let mut group = c.benchmark_group("SubNoBorrow");

    let m: B = UniformRand::rand(&mut rng);
    let n: B = UniformRand::rand(&mut rng);
    group.bench_with_input(repr, &(m, &n), |b, &(mut m, n)| {
        b.iter(|| black_box(m.sub_noborrow(n)))
    });

    group.finish();

    let mut group = c.benchmark_group("Mul2");

    let m: B = UniformRand::rand(&mut rng);
    group.bench_with_input(repr, &(m), |b, &(mut m)| b.iter(|| black_box(m.mul2())));

    group.finish();

    let mut group = c.benchmark_group("Div2");

    let m: B = UniformRand::rand(&mut rng);
    group.bench_with_input(repr, &(m), |b, &(mut m)| b.iter(|| black_box(m.div2())));

    group.finish();
}

#[allow(dead_code)]
pub fn square_root_field_bench<F: SquareRootField>(c: &mut Criterion, params: &str, repr: &str) {
    let mut rng = ark_std::test_rng();

    let mut group = c.benchmark_group("Sqrt");

    let m: F = UniformRand::rand(&mut rng);
    let m = m.square();
    group.bench_with_input(BenchmarkId::new(params, repr), &m, |b, m| {
        b.iter(|| black_box(m.sqrt()))
    });

    group.finish();
}
