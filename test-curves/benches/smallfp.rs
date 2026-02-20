use ark_algebra_bench_templates::*;
use ark_ff::fields::{Fp64, MontBackend, MontConfig, SmallFp, SmallFpConfig};
use ark_test_curves::{smallfp32::SmallFp32M31, smallfp64::SmallFp64Goldilock};

#[derive(MontConfig)]
#[modulus = "18446744069414584321"]
#[generator = "7"]
pub struct F64Config;
pub type F64 = Fp64<MontBackend<F64Config, 1>>;

#[derive(MontConfig)]
#[modulus = "2147483647"]
#[generator = "7"]
pub struct F32Config;
pub type F32 = Fp64<MontBackend<F32Config, 1>>;

#[derive(MontConfig)]
#[modulus = "65521"]
#[generator = "17"]
pub struct F16Config;
pub type F16 = Fp64<MontBackend<F16Config, 1>>;

#[derive(SmallFpConfig)]
#[modulus = "65521"]
#[generator = "17"]
pub struct SmallFp16Config;
pub type SmallFp16 = SmallFp<SmallFp16Config>;

#[derive(MontConfig)]
#[modulus = "251"]
#[generator = "6"]
pub struct F8Config;
pub type F8 = Fp64<MontBackend<F8Config, 1>>;

#[derive(SmallFpConfig)]
#[modulus = "251"]
#[generator = "6"]
pub struct SmallFp8Config;
pub type SmallFp8 = SmallFp<SmallFp8Config>;

f_bench!(prime, "F8", F8);
f_bench!(prime, "SmallF8Mont", SmallFp8);

f_bench!(prime, "F16", F16);
f_bench!(prime, "SmallF16Mont", SmallFp16);

f_bench!(prime, "F32", F32);
f_bench!(prime, "SmallF32Mont", SmallFp32M31);

f_bench!(prime, "F64", F64);
f_bench!(prime, "SmallF64Mont", SmallFp64Goldilock);

criterion_main!(
    f8::benches,
    smallfp8::benches,
    f16::benches,
    smallfp16::benches,
    f32::benches,
    smallfp32m31::benches,
    f64::benches,
    smallfp64goldilock::benches,
);
