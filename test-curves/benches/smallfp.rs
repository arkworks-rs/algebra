use ark_algebra_bench_templates::*;
use ark_ff::fields::{Fp64, MontBackend, MontConfig};
use ark_test_curves::{
    smallfp32::{SmallF32, SmallF32Mont},
    smallfp64::{SmallF64, SmallF64Mont},
};

#[derive(MontConfig)]
#[modulus = "18446744069414584321"]
#[generator = "7"]
pub struct F64Config;
pub type F64 = Fp64<MontBackend<F64Config, 1>>;

#[derive(MontConfig)]
#[modulus = "2147483647"]
#[generator = "3"]
pub struct F32Config;
pub type F32 = Fp64<MontBackend<F32Config, 1>>;

f_bench!(prime, "F32", F32);
f_bench!(prime, "SmallF32", SmallF32);
f_bench!(prime, "SmallF32Mont", SmallF32Mont);

f_bench!(prime, "F64", F64);
f_bench!(prime, "SmallF64", SmallF64);
f_bench!(prime, "SmallF64Mont", SmallF64Mont);

criterion_main!(
    f32::benches,
    smallf32::benches,
    smallf32mont::benches,
    f64::benches,
    smallf64::benches,
    smallf64mont::benches,
);
