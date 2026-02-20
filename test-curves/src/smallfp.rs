use ark_ff::{MontConfig, SmallFp};

#[derive(MontConfig)]
#[modulus = "251"]
#[generator = "6"]
pub struct SmallFp8Config;
pub type SmallFp8 = SmallFp<SmallFp8Config>;

#[derive(MontConfig)]
#[modulus = "127"]
#[generator = "3"]
pub struct SmallFp8ConfigM7;
pub type SmallFp8M7 = SmallFp<SmallFp8ConfigM7>;

#[derive(MontConfig)]
#[modulus = "65521"]
#[generator = "17"]
pub struct SmallFp16Config;
pub type SmallFp16 = SmallFp<SmallFp16Config>;

#[derive(MontConfig)]
#[modulus = "8191"]
#[generator = "17"]
pub struct SmallFp16ConfigM13;
pub type SmallFp16M13 = SmallFp<SmallFp16ConfigM13>;

#[derive(MontConfig)]
#[modulus = "2147483647"]
#[generator = "7"]
pub struct SmallFp32ConfigM31;
pub type SmallFp32M31 = SmallFp<SmallFp32ConfigM31>;

#[derive(MontConfig)]
#[modulus = "2013265921"]
#[generator = "31"]
pub struct SmallFpBabybearConfig;
pub type SmallFp32Babybear = SmallFp<SmallFpBabybearConfig>;

#[derive(MontConfig)]
#[modulus = "18446744069414584321"] // Goldilocks prime 2^64 - 2^32 + 1
#[generator = "7"]
pub struct SmallFp64GoldilockConfig;
pub type SmallFp64Goldilock = SmallFp<SmallFp64GoldilockConfig>;

#[derive(MontConfig)]
#[modulus = "143244528689204659050391023439224324689"]
#[generator = "3"]
pub struct SmallFp128Config;
pub type SmallFp128 = SmallFp<SmallFp128Config>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f8; SmallFp8);
    test_small_field!(f8_m7; SmallFp8M7);
    test_small_field!(f16; SmallFp16);
    test_small_field!(f16_m13; SmallFp16M13);
    test_small_field!(f32_m31; SmallFp32M31);
    test_small_field!(f32_babybear; SmallFp32Babybear);
    test_small_field!(f64_goldilock; SmallFp64Goldilock);
    test_small_field!(f128; SmallFp128);
}
