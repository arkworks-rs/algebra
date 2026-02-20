use ark_ff::{SmallFp, SmallFpConfig};

#[derive(SmallFpConfig)]
#[modulus = "18446744069414584321"] // Goldilock's prime 2^64 - 2^32 + 1
#[generator = "7"]
pub struct SmallFp64GoldilockConfig;
pub type SmallFp64Goldilock = SmallFp<SmallFp64GoldilockConfig>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f64; SmallFp64Goldilock);
}
