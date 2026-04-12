use ark_algebra_bench_templates::*;
use ark_ff::fields::{Fp64, MontBackend, MontConfig};
use ark_ff::test_helpers::smallfp::{
    SmallFp16, SmallFp32Babybear, SmallFp32Koalabear, SmallFp32M31, SmallFp64Goldilock, SmallFp8,
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

#[derive(MontConfig)]
#[modulus = "251"]
#[generator = "6"]
pub struct F8Config;
pub type F8 = Fp64<MontBackend<F8Config, 1>>;

f_bench!(prime, "F8", F8);
f_bench!(prime, "SmallF8Mont", SmallFp8);

f_bench!(prime, "F16", F16);
f_bench!(prime, "SmallF16Mont", SmallFp16);

f_bench!(prime, "F32", F32);
f_bench!(prime, "SmallF32Mont", SmallFp32M31);
f_bench!(prime, "SmallF32MontBabybear", SmallFp32Babybear);
f_bench!(prime, "SmallF32MontKoalabear", SmallFp32Koalabear);

f_bench!(prime, "F64", F64);
f_bench!(prime, "SmallF64Mont", SmallFp64Goldilock);

criterion_main!(
    f8::benches,
    smallfp8::benches,
    f16::benches,
    smallfp16::benches,
    f32::benches,
    smallfp32m31::benches,
    smallfp32babybear::benches,
    smallfp32koalabear::benches,
    f64::benches,
    smallfp64goldilock::benches,
);
