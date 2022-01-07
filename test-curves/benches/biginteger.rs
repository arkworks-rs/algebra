#[macro_use]
extern crate criterion;

use ark_test_curves::{
    BigInteger128, BigInteger256, BigInteger320, BigInteger384, BigInteger448, BigInteger64,
    BigInteger768, BigInteger832,
};
use criterion::Criterion;

mod templates;

fn bench_biginteger(c: &mut Criterion) {
    templates::biginteger_bench::<BigInteger64>(c, "BigInteger64");
    templates::biginteger_bench::<BigInteger128>(c, "BigInteger128");
    templates::biginteger_bench::<BigInteger256>(c, "BigInteger256");
    templates::biginteger_bench::<BigInteger320>(c, "BigInteger320");
    templates::biginteger_bench::<BigInteger384>(c, "BigInteger384");
    templates::biginteger_bench::<BigInteger448>(c, "BigInteger448");
    templates::biginteger_bench::<BigInteger768>(c, "BigInteger768");
    templates::biginteger_bench::<BigInteger832>(c, "BigInteger832");
}

criterion_group!(benches, bench_biginteger);
criterion_main!(benches);
