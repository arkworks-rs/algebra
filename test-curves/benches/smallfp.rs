use ark_algebra_bench_templates::*;
use ark_ff::fields::{Fp64, MontBackend, MontConfig, SmallFp, SmallFpConfig};
use ark_test_curves::{
    smallfp32::{SmallF32MontM31},
    smallfp64::{SmallF64MontGoldilock},
};


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
#[backend = "montgomery"]
pub struct F16ConfigMont;
pub type SmallF16Mont = SmallFp<F16ConfigMont>;

#[derive(MontConfig)]
#[modulus = "251"]
#[generator = "6"]
pub struct F8Config;
pub type F8 = Fp64<MontBackend<F8Config, 1>>;

#[derive(SmallFpConfig)]
#[modulus = "251"]
#[generator = "6"]
#[backend = "montgomery"]
pub struct SmallF8ConfigMont;
pub type SmallF8Mont = SmallFp<SmallF8ConfigMont>;



f_bench!(prime, "F8", F8);
f_bench!(prime, "SmallF8Mont", SmallF8Mont);

f_bench!(prime, "F16", F16);
f_bench!(prime, "SmallF16Mont", SmallF16Mont);

f_bench!(prime, "F32", F32);
f_bench!(prime, "SmallF32Mont", SmallF32MontM31);

f_bench!(prime, "F64", F64);
f_bench!(prime, "SmallF64Mont", SmallF64MontGoldilock);

criterion_main!(
    f8::benches,
    smallf8mont::benches,
    f16::benches,
    smallf16mont::benches,
    f32::benches,
    smallf32montm31::benches,
    f64::benches,
    smallf64montgoldilock::benches,
);
