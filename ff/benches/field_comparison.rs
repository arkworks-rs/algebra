use ark_ff::ark_ff_macros::SmallFpConfig;
use ark_ff::fields::{Fp128, Fp64, MontBackend, MontConfig};
use ark_ff::{BigInt, SmallFp, SmallFpConfig, SqrtPrecomputation};
use ark_std::hint::black_box;
use criterion::{criterion_group, criterion_main, Criterion};
use p3_field::AbstractField;
use p3_goldilocks::Goldilocks as P3Goldilocks;

// Goldilock's prime from Plonk3 18446744069414584321;

#[derive(SmallFpConfig)]
#[modulus = "18446744069414584321"]
#[generator = "2"]
#[backend = "standard"]
pub struct SmallF64Config;
pub type SmallF64 = SmallFp<SmallF64Config>;

#[derive(SmallFpConfig)]
#[modulus = "18446744069414584321"]
#[generator = "2"]
#[backend = "montgomery"]
pub struct SmallF64ConfigMont;
pub type SmallF64Mont = SmallFp<SmallF64ConfigMont>;

#[derive(SmallFpConfig)]
#[modulus = "18446744069414584321"]
#[generator = "2"]
#[backend = "standard"]
pub struct SmallF128Config;
pub type SmallF128 = SmallFp<SmallF128Config>;

#[derive(SmallFpConfig)]
#[modulus = "143244528689204659050391023439224324689"]
#[generator = "2"]
#[backend = "montgomery"]
pub struct SmallF128ConfigMont;
pub type SmallF128Mont = SmallFp<SmallF128ConfigMont>;

#[derive(MontConfig)]
#[modulus = "18446744069414584321"]
#[generator = "2"]
pub struct F64Config;
pub type F64 = Fp64<MontBackend<F64Config, 1>>;

#[derive(MontConfig)]
#[modulus = "143244528689204659050391023439224324689"]
#[generator = "2"]
pub struct F128Config;
pub type F128 = Fp128<MontBackend<F128Config, 2>>;

// Benchmark functions

fn naive_element_wise_mult_ark_bigint_64(c: &mut Criterion) {
    // let's get four vectors and multiply them element-wise
    let len = 2_i64.pow(22);
    let v1: Vec<F64> = (0..len).map(F64::from).collect();
    let v2: Vec<F64> = (0..len).map(F64::from).collect();
    let v3: Vec<F64> = (0..len).map(F64::from).collect();
    let v4: Vec<F64> = (0..len).map(F64::from).collect();
    let mut element_wise_product: Vec<F64> = vec![F64::from(0); len as usize];

    c.bench_function("naive_element_wise_mult_ark_bigint_64", |b| {
        b.iter(|| {
            for i in 0..len as usize {
                element_wise_product[i] = v1.get(i).unwrap()
                    * v2.get(i).unwrap()
                    * v3.get(i).unwrap()
                    * v4.get(i).unwrap();
            }
            black_box(element_wise_product.clone());
        })
    });
}

fn naive_element_wise_mult_ark_small_field_64_std(c: &mut Criterion) {
    // let's get four vectors and multiply them element-wise
    let len = 2_i64.pow(22);
    let v1: Vec<SmallF64> = (0..len).map(|i| SmallF64::from(i as u32)).collect();
    let v2: Vec<SmallF64> = (0..len).map(|i| SmallF64::from(i as u32)).collect();
    let v3: Vec<SmallF64> = (0..len).map(|i| SmallF64::from(i as u32)).collect();
    let v4: Vec<SmallF64> = (0..len).map(|i| SmallF64::from(i as u32)).collect();
    let mut element_wise_product: Vec<SmallF64> = vec![SmallF64::from(0u32); len as usize];

    c.bench_function("naive_element_wise_mult_ark_small_field_64_std", |b| {
        b.iter(|| {
            for i in 0..len as usize {
                element_wise_product[i] = v1.get(i).unwrap()
                    * v2.get(i).unwrap()
                    * v3.get(i).unwrap()
                    * v4.get(i).unwrap();
            }
            black_box(&element_wise_product);
        })
    });
}

fn naive_element_wise_mult_ark_small_field_64_mont(c: &mut Criterion) {
    // let's get four vectors and multiply them element-wise
    let len = 2_i64.pow(22);
    let v1: Vec<SmallF64Mont> = (0..len).map(|i| SmallF64Mont::from(i as u32)).collect();
    let v2: Vec<SmallF64Mont> = (0..len).map(|i| SmallF64Mont::from(i as u32)).collect();
    let v3: Vec<SmallF64Mont> = (0..len).map(|i| SmallF64Mont::from(i as u32)).collect();
    let v4: Vec<SmallF64Mont> = (0..len).map(|i| SmallF64Mont::from(i as u32)).collect();
    let mut element_wise_product: Vec<SmallF64Mont> = vec![SmallF64Mont::from(0u32); len as usize];

    c.bench_function("naive_element_wise_mult_ark_small_field_64_mont", |b| {
        b.iter(|| {
            for i in 0..len as usize {
                element_wise_product[i] = v1.get(i).unwrap()
                    * v2.get(i).unwrap()
                    * v3.get(i).unwrap()
                    * v4.get(i).unwrap();
            }
            black_box(&element_wise_product);
        })
    });
}

fn naive_element_wise_mult_p3_64(c: &mut Criterion) {
    // let's get four vectors and multiply them element-wise
    let len = 2_i64.pow(22);
    let v1: Vec<P3Goldilocks> = (0..len)
        .map(|i| P3Goldilocks::from_canonical_u64(i as u64))
        .collect();
    let v2: Vec<P3Goldilocks> = (0..len)
        .map(|i| P3Goldilocks::from_canonical_u64(i as u64))
        .collect();
    let v3: Vec<P3Goldilocks> = (0..len)
        .map(|i| P3Goldilocks::from_canonical_u64(i as u64))
        .collect();
    let v4: Vec<P3Goldilocks> = (0..len)
        .map(|i| P3Goldilocks::from_canonical_u64(i as u64))
        .collect();
    let mut element_wise_product: Vec<P3Goldilocks> =
        vec![P3Goldilocks::from_canonical_u64(0_u64); len as usize];

    c.bench_function("naive_element_wise_mult_p3_64", |b| {
        b.iter(|| {
            for i in 0..len as usize {
                element_wise_product[i] = *v1.get(i).unwrap()
                    * *v2.get(i).unwrap()
                    * *v3.get(i).unwrap()
                    * *v4.get(i).unwrap();
            }
            black_box(element_wise_product.clone());
        })
    });
}

fn naive_element_wise_mult_ark_bigint_128(c: &mut Criterion) {
    // let's get four vectors and multiply them element-wise
    let len = 2_i64.pow(22);
    let v1: Vec<F128> = (0..len).map(F128::from).collect();
    let v2: Vec<F128> = (0..len).map(F128::from).collect();
    let v3: Vec<F128> = (0..len).map(F128::from).collect();
    let v4: Vec<F128> = (0..len).map(F128::from).collect();
    let mut element_wise_product: Vec<F128> = vec![F128::from(0); len as usize];

    c.bench_function("naive_element_wise_mult_ark_bigint_128", |b| {
        b.iter(|| {
            for i in 0..len as usize {
                element_wise_product[i] = v1.get(i).unwrap()
                    * v2.get(i).unwrap()
                    * v3.get(i).unwrap()
                    * v4.get(i).unwrap();
            }
            black_box(element_wise_product.clone());
        })
    });
}

fn naive_element_wise_mult_ark_small_field_128(c: &mut Criterion) {
    let len = 2_i64.pow(22);
    let v1: Vec<SmallF128> = (0..len).map(SmallF128::from).collect();
    let v2: Vec<SmallF128> = (0..len).map(SmallF128::from).collect();
    let v3: Vec<SmallF128> = (0..len).map(SmallF128::from).collect();
    let v4: Vec<SmallF128> = (0..len).map(SmallF128::from).collect();
    let mut element_wise_product: Vec<SmallF128> = vec![SmallF128::from(0); len as usize];

    c.bench_function("naive_element_wise_mult_ark_small_field", |b| {
        b.iter(|| {
            for i in 0..len as usize {
                element_wise_product[i] = v1.get(i).unwrap()
                    * v2.get(i).unwrap()
                    * v3.get(i).unwrap()
                    * v4.get(i).unwrap();
            }
            black_box(element_wise_product.clone());
        })
    });
}

criterion_group!(
    benches,
    naive_element_wise_mult_ark_bigint_64,
    naive_element_wise_mult_ark_small_field_64_std,
    naive_element_wise_mult_ark_small_field_64_mont,
    naive_element_wise_mult_p3_64,
    naive_element_wise_mult_ark_bigint_128,
    naive_element_wise_mult_ark_small_field_128,
);
criterion_main!(benches);
