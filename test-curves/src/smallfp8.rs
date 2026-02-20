use ark_ff::{SmallFp, SmallFpConfig};

#[derive(SmallFpConfig)]
#[modulus = "251"]
#[generator = "6"]
pub struct SmallFp8Config;
pub type SmallFp8 = SmallFp<SmallFp8Config>;

#[derive(SmallFpConfig)]
#[modulus = "127"]
#[generator = "3"]
pub struct SmallFp8ConfigM7;
pub type SmallFp8M7 = SmallFp<SmallFp8ConfigM7>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f8; SmallFp8);
    test_small_field!(f8_mont_m7; SmallFp8M7);
}
