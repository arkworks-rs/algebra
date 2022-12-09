//! Prime field `Fp` where `p = 2^127 - 1`.
use ark_ff::fields::{Fp128, MontBackend};

#[derive(ark_ff::MontConfig)]
#[modulus = "170141183460469231731687303715884105727"]
#[generator = "43"]
pub struct FqConfig;
pub type Fq = Fp128<MontBackend<FqConfig, 2>>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    test_field!(fq; Fq; mont_prime_field);
}
