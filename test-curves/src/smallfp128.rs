use ark_ff::{SmallFp, SmallFpConfig};

#[derive(SmallFpConfig)]
#[modulus = "143244528689204659050391023439224324689"]
#[generator = "3"]
pub struct SmallFp128Config;
pub type SmallFp128 = SmallFp<SmallFp128Config>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f128; SmallFp128);
}
