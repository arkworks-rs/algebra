use ark_ff::{SmallFp, SmallFpConfig};

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
pub type SmallF32MontM31 = SmallFp<SmallFieldMont>;

#[derive(SmallFpConfig)]
#[modulus = "2013265921"]
#[generator = "31"]
#[backend = "montgomery"]
pub struct SmallFieldMontBabybear;
pub type SmallF32MontBabybear = SmallFp<SmallFieldMontBabybear>;


#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f32; SmallF32);
    test_small_field!(f32_mont_m31; SmallF32MontM31);
    test_small_field!(f32_mont_babybear; SmallF32MontBabybear);
}
