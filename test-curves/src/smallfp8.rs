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

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f8; SmallF8);
    test_small_field!(f8_mont; SmallF8Mont);
}
