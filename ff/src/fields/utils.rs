use num_bigint::BigUint;
use num_traits::{One, Zero};

/// Calculates the k-adicity of n, i.e., the number of trailing 0s in a base-k
/// representation.
pub fn k_adicity(k: u64, mut n: &BigUint) -> u32 {
    let mut n = n.clone();
    let one = BigUint::one();
    let mut r = 0;
    while n > one {
        if (n % k).is_zero() {
            r += 1u32;
            n /= k;
        } else {
            return r;
        }
    }
    r
}
