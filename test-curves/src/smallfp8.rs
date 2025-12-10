use ark_ff::{SmallFp, SmallFpConfig};

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
#[modulus = "127"]
#[generator = "3"]
#[backend = "montgomery"]
pub struct SmallF8ConfigMontM7;
pub type SmallF8MontM7 = SmallFp<SmallF8ConfigMontM7>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f8; SmallF8);
    test_small_field!(f8_mont; SmallF8Mont);
    test_small_field!(f8_mont_m7; SmallF8MontM7);
}
