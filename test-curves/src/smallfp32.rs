use ark_ff::{SmallFp, SmallFpConfig};

#[derive(SmallFpConfig)]
#[modulus = "2147483647"]
#[generator = "7"]
pub struct SmallFp32ConfigM31;
pub type SmallFp32M31 = SmallFp<SmallFp32ConfigM31>;

#[derive(SmallFpConfig)]
#[modulus = "2013265921"]
#[generator = "31"]
pub struct SmallFpBabybearConfig;
pub type SmallFp32Babybear = SmallFp<SmallFpBabybearConfig>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f32; SmallFp32M31);
    test_small_field!(f32_mont_babybear; SmallFp32Babybear);
}
