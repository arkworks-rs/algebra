use ark_ff::ark_ff_macros::SmallFpConfig;
use ark_ff::{BigInt, SmallFp, SmallFpConfig, SqrtPrecomputation};

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

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f32; SmallF32);
    test_small_field!(f32_mont; SmallF32Mont);
}
