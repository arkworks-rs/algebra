use ark_algebra_test_templates::*;
use ark_ff::ark_ff_macros::SmallFpConfig;
use ark_ff::{BigInt, SmallFp, SmallFpConfig, SqrtPrecomputation};

#[derive(SmallFpConfig)]
#[modulus = "251"]
#[generator = "6"]
#[backend = "standard"]
pub struct SmallF8Config;
pub type SmallF8 = SmallFp<SmallF8Config>;

#[derive(SmallFpConfig)]
#[modulus = "251"]
#[generator = "6"]
#[backend = "montgomery"]
pub struct SmallF8ConfigMont;
pub type SmallF8Mont = SmallFp<SmallF8ConfigMont>;

#[derive(SmallFpConfig)]
#[modulus = "65521"]
#[generator = "17"]
#[backend = "standard"]
pub struct SmallF16Config;
pub type SmallF16 = SmallFp<SmallF16Config>;

#[derive(SmallFpConfig)]
#[modulus = "65521"]
#[generator = "17"]
#[backend = "montgomery"]
pub struct SmallF16ConfigMont;
pub type SmallF16Mont = SmallFp<SmallF16ConfigMont>;

#[derive(SmallFpConfig)]
#[modulus = "2147483647"] // m31
#[generator = "7"]
#[backend = "standard"]
pub struct SmallField;
pub type SmallF32 = SmallFp<SmallField>;

#[derive(SmallFpConfig)]
#[modulus = "2147483647"] // m31
#[generator = "7"]
#[backend = "montgomery"]
pub struct SmallFieldMont;
pub type SmallF32Mont = SmallFp<SmallFieldMont>;

#[derive(SmallFpConfig)]
#[modulus = "18446744069414584321"] // Goldilock's prime 2^64 - 2^32 + 1
#[generator = "7"]
#[backend = "standard"]
pub struct SmallF64Config;
pub type SmallF64 = SmallFp<SmallF64Config>;

#[derive(SmallFpConfig)]
#[modulus = "18446744069414584321"] // Goldilock's prime 2^64 - 2^32 + 1
#[generator = "7"]
#[backend = "montgomery"]
pub struct SmallF64ConfigMont;
pub type SmallF64Mont = SmallFp<SmallF64ConfigMont>;

#[derive(SmallFpConfig)]
#[modulus = "143244528689204659050391023439224324689"]
#[generator = "3"]
#[backend = "standard"]
pub struct SmallF128Config;
pub type SmallF128 = SmallFp<SmallF128Config>;

#[derive(SmallFpConfig)]
#[modulus = "143244528689204659050391023439224324689"]
#[generator = "3"]
#[backend = "montgomery"]
pub struct SmallF128ConfigMont;
pub type SmallF128Mont = SmallFp<SmallF128ConfigMont>;

test_small_field!(f8; SmallF8);
test_small_field!(f16; SmallF16);
test_small_field!(f32; SmallF32);
test_small_field!(f64; SmallF64);
test_small_field!(f128; SmallF128);

test_small_field!(f8_mont; SmallF8Mont);
test_small_field!(f16_mont; SmallF16Mont);
test_small_field!(f32_mont; SmallF32Mont);
test_small_field!(f64_mont; SmallF64Mont);
test_small_field!(f128_mont; SmallF128Mont);
