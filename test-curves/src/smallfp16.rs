use ark_ff::ark_ff_macros::SmallFpConfig;
use ark_ff::{BigInt, SmallFp, SmallFpConfig, SqrtPrecomputation};

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

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f16; SmallF16);
    test_small_field!(f16_mont; SmallF16Mont);
}
