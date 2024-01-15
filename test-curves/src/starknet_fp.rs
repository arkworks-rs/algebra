//! Prime field `Fq` where `q =  2^251 + 17 * 2^192 + 1` is the StarkNet prime.
use ark_ff::fields::{Fp256, MontBackend};

#[derive(ark_ff::MontConfig)]
#[modulus = "3618502788666131213697322783095070105623107215331596699973092056135872020481"]
#[generator = "3"]
pub struct FqConfig;
pub type Fq = Fp256<MontBackend<FqConfig, 4>>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    test_field!(fp; Fq; mont_prime_field);
}
