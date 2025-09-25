use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

fn mult_u128(c: &mut Criterion) {
    c.bench_function("u128_mult", |b| {
        b.iter(|| {
            let a: u8 = 5;
            let b: u8 = 254;
            let c: u128 = (a as u128) * (b as u128);
            black_box((c % 255) as u8);
        })
    });
}

fn mult_u16(c: &mut Criterion) {
    c.bench_function("u16_mult", |b| {
        b.iter(|| {
            let a: u8 = 5;
            let b: u8 = 254;
            let c: u16 = (a as u16) * (b as u16);
            black_box((c % 255) as u8);
        })
    });
}

fn add_u128(c: &mut Criterion) {
    c.bench_function("u128_add", |b| {
        b.iter(|| {
            let a: u8 = 5;
            let b: u8 = 254;
            let c: u128 = (a as u128) + (b as u128);
            black_box((c % 255) as u8);
        })
    });
}

fn add_u16(c: &mut Criterion) {
    c.bench_function("u8_add", |b| {
        b.iter(|| {
            let a: u8 = 5;
            let b: u8 = 25;
            let c: u8 = a + b;
            black_box((c % 255) as u8);
        })
    });
}

criterion_group!(benches, mult_u128, mult_u16, add_u128, add_u16);
criterion_main!(benches);
