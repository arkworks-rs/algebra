use ark_ff::{SmallFp, SmallFpConfig};

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
#[modulus = "8191"]
#[generator = "17"]
#[backend = "montgomery"]
pub struct SmallF16ConfigMontM13;
pub type SmallF16MontM13 = SmallFp<SmallF16ConfigMontM13>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f16; SmallF16);
    test_small_field!(f16_mont; SmallF16Mont);
    test_small_field!(f16_mont_m13; SmallF16MontM13);
}
