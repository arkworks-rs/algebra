use ark_ff::define_field;

define_field!(modulus = "251", generator = "6", name = SmallFp8,);

define_field!(modulus = "65521", generator = "17", name = SmallFp16,);

// Mersenne13 prime 2^13 - 1
define_field!(modulus = "8191", generator = "17", name = SmallFp16M13,);

// Mersenne31 prime 2^31 - 1
define_field!(modulus = "2147483647", generator = "7", name = SmallFp32M31,);

// Babybear prime 2^31 - 2^27 + 1
define_field!(
    modulus = "2013265921",
    generator = "31",
    name = SmallFp32Babybear,
);

// Goldilocks prime 2^64 - 2^32 + 1
define_field!(
    modulus = "18446744069414584321",
    generator = "7",
    name = SmallFp64Goldilock,
);

define_field!(
    modulus = "143244528689204659050391023439224324689",
    generator = "3",
    name = SmallFp128,
);

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f8; SmallFp8);
    test_small_field!(f16; SmallFp16);
    test_small_field!(f16_mont_m13; SmallFp16M13);
    test_small_field!(f32; SmallFp32M31);
    test_small_field!(f32_mont_babybear; SmallFp32Babybear);
    test_small_field!(f64; SmallFp64Goldilock);
    test_small_field!(f128; SmallFp128);
}
