use num_bigint::BigUint;
use num_traits::Zero;

/// Calculates the k-adicity of n, i.e., the number of trailing 0s in a base-k
/// representation.
pub const fn k_adicity(k: u64, mut n: u64) -> u32 {
    if n == 0 {
        return 0;
    }
    let mut r = 0;
    while n % k == 0 {
        r += 1;
        n /= k;
    }
    r
}

/// Calculates the k-adicity of n, i.e., the number of trailing 0s in a base-k
/// representation.
pub fn k_adicity_big_int(k: BigUint, mut n: BigUint) -> u32 {
    if n.is_zero() {
        return 0;
    }
    let mut r = 0;
    while (&n % &k).is_zero() {
        r += 1;
        n /= &k;
    }
    r
}
