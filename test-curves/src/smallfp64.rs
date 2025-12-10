use ark_ff::{SmallFp, SmallFpConfig};

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
pub type SmallF64MontGoldilock = SmallFp<SmallF64ConfigMont>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f64; SmallF64);
    test_small_field!(f64_mont; SmallF64MontGoldilock);
}
