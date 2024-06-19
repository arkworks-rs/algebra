use crate::{biginteger::BigInteger, UniformRand};
use num_bigint::BigUint;

// Test elementary math operations for BigInteger.
fn biginteger_arithmetic_test<B: BigInteger>(a: B, b: B, zero: B, max: B) {
    // zero == zero
    assert_eq!(zero, zero);

    // zero.is_zero() == true
    assert_eq!(zero.is_zero(), true);

    // a == a
    assert_eq!(a, a);

    // a + 0 = a
    let mut a0_add = a;
    let carry = a0_add.add_with_carry(&zero);
    assert_eq!(a0_add, a);
    assert_eq!(carry, false);

    // a - 0 = a
    let mut a0_sub = a;
    let borrow = a0_sub.sub_with_borrow(&zero);
    assert_eq!(a0_sub, a);
    assert_eq!(borrow, false);

    // a - a = 0
    let mut aa_sub = a;
    let borrow = aa_sub.sub_with_borrow(&a);
    assert_eq!(aa_sub, zero);
    assert_eq!(borrow, false);

    // a + b = b + a
    let mut ab_add = a;
    let ab_carry = ab_add.add_with_carry(&b);
    let mut ba_add = b;
    let ba_carry = ba_add.add_with_carry(&a);
    assert_eq!(ab_add, ba_add);
    assert_eq!(ab_carry, ba_carry);

    // a * 1 = a
    let mut a_mul1 = a;
    a_mul1 <<= 0;
    assert_eq!(a_mul1, a);

    // a * 2 = a + a
    let mut a_mul2 = a;
    a_mul2.mul2();
    let mut a_plus_a = a;
    let carry_a_plus_a = a_plus_a.add_with_carry(&a); // Won't assert anything about carry bit.
    assert_eq!(a_mul2, a_plus_a);

    // a * 1 = a
    assert_eq!(a.mul_low(&B::from(1u64)), a);

    // a * 2 = a
    assert_eq!(a.mul_low(&B::from(2u64)), a_plus_a);

    // a * b = b * a
    assert_eq!(a.mul_low(&b), b.mul_low(&a));

    // a * 2 * b * 0 = 0
    assert!(a.mul_low(&zero).is_zero());

    // a * 2 * ... * 2  = a * 2^n
    let mut a_mul_n = a;
    for _ in 0..20 {
        a_mul_n = a_mul_n.mul_low(&B::from(2u64));
    }
    assert_eq!(a_mul_n, a << 20);

    // a * 0 = (0, 0)
    assert_eq!(a.mul(&zero), (zero, zero));

    // a * 1 = (a, 0)
    assert_eq!(a.mul(&B::from(1u64)), (a, zero));

    // a * 1 = 0 (high part of the result)
    assert_eq!(a.mul_high(&B::from(1u64)), (zero));

    // a * 0 = 0 (high part of the result)
    assert!(a.mul_high(&zero).is_zero());

    // If a + a has a carry
    if carry_a_plus_a {
        // a + a has a carry: high part of a * 2 is not zero
        assert_ne!(a.mul_high(&B::from(2u64)), zero);
    } else {
        // a + a has no carry: high part of a * 2 is zero
        assert_eq!(a.mul_high(&B::from(2u64)), zero);
    }

    // max + max = max * 2
    let mut max_plus_max = max;
    max_plus_max.add_with_carry(&max);
    assert_eq!(max.mul(&B::from(2u64)), (max_plus_max, B::from(1u64)));
    assert_eq!(max.mul_high(&B::from(2u64)), B::from(1u64));
}

fn biginteger_shr<B: BigInteger>() {
    let mut rng = ark_std::test_rng();
    let a = B::rand(&mut rng);
    assert_eq!(a >> 0, a);

    // Binary simple test
    let a = B::from(256u64);
    assert_eq!(a >> 2, B::from(64u64));

    // Test saturated underflow
    let a = B::from(1u64);
    assert_eq!(a >> 5, B::from(0u64));

    // Test null bits
    let a = B::rand(&mut rng);
    let b = a >> 3;
    assert_eq!(b.get_bit(B::NUM_LIMBS * 64 - 1), false);
    assert_eq!(b.get_bit(B::NUM_LIMBS * 64 - 2), false);
    assert_eq!(b.get_bit(B::NUM_LIMBS * 64 - 3), false);
}

fn biginteger_shl<B: BigInteger>() {
    let mut rng = ark_std::test_rng();
    let a = B::rand(&mut rng);
    assert_eq!(a << 0, a);

    // Binary simple test
    let a = B::from(64u64);
    assert_eq!(a << 2, B::from(256u64));

    // Testing saturated overflow
    let a = B::rand(&mut rng);
    assert_eq!(a << ((B::NUM_LIMBS as u32) * 64), B::from(0u64));

    // Test null bits
    let a = B::rand(&mut rng);
    let b = a << 3;
    assert_eq!(b.get_bit(0), false);
    assert_eq!(b.get_bit(1), false);
    assert_eq!(b.get_bit(2), false);
}

// Test for BigInt's bitwise operations
fn biginteger_bitwise_ops_test<B: BigInteger>() {
    let mut rng = ark_std::test_rng();

    // Test XOR
    // a xor a = 0
    let a = B::rand(&mut rng);
    assert_eq!(a ^ &a, B::from(0_u64));

    // Testing a xor b xor b
    let a = B::rand(&mut rng);
    let b = B::rand(&mut rng);
    let xor_ab = a ^ b;
    assert_eq!(xor_ab ^ b, a);

    // Test OR
    // a or a = a
    let a = B::rand(&mut rng);
    assert_eq!(a | &a, a);

    // Testing a or b or b
    let a = B::rand(&mut rng);
    let b = B::rand(&mut rng);
    let or_ab = a | b;
    assert_eq!(or_ab | &b, a | b);

    // Test AND
    // a and a = a
    let a = B::rand(&mut rng);
    assert_eq!(a & (&a), a);

    // Testing a and a and b.
    let a = B::rand(&mut rng);
    let b = B::rand(&mut rng);
    let b_clone = b.clone();
    let and_ab = a & b;
    assert_eq!(and_ab & b_clone, a & b);

    // Testing De Morgan's law
    let a = 0x1234567890abcdef_u64;
    let b = 0xfedcba0987654321_u64;
    let de_morgan_lhs = B::from(!(a | b));
    let de_morgan_rhs = B::from(!a) & B::from(!b);
    assert_eq!(de_morgan_lhs, de_morgan_rhs);
}

// Test correctness of BigInteger's bit values
fn biginteger_bits_test<B: BigInteger>() {
    let mut one = B::from(1u64);
    // 0th bit of BigInteger representing 1 is 1
    assert!(one.get_bit(0));
    // 1st bit of BigInteger representing 1 is not 1
    assert!(!one.get_bit(1));
    one <<= 5;
    let thirty_two = one;
    // 0th bit of BigInteger representing 32 is not 1
    assert!(!thirty_two.get_bit(0));
    // 1st bit of BigInteger representing 32 is not 1
    assert!(!thirty_two.get_bit(1));
    // 2nd bit of BigInteger representing 32 is not 1
    assert!(!thirty_two.get_bit(2));
    // 3rd bit of BigInteger representing 32 is not 1
    assert!(!thirty_two.get_bit(3));
    // 4th bit of BigInteger representing 32 is not 1
    assert!(!thirty_two.get_bit(4));
    // 5th bit of BigInteger representing 32 is 1
    assert!(thirty_two.get_bit(5), "{:?}", thirty_two);

    // Generates a random BigInteger and tests bit construction methods.
    let mut rng = ark_std::test_rng();
    let a: B = UniformRand::rand(&mut rng);
    assert_eq!(B::from_bits_be(&a.to_bits_be()), a);
    assert_eq!(B::from_bits_le(&a.to_bits_le()), a);
}

// Test conversion from BigInteger to BigUint
fn biginteger_conversion_test<B: BigInteger>() {
    let mut rng = ark_std::test_rng();

    let x: B = UniformRand::rand(&mut rng);
    let x_bigint: BigUint = x.into();
    let x_recovered = B::try_from(x_bigint).ok().unwrap();

    assert_eq!(x, x_recovered);
}

// Wrapper test function for BigInteger
fn test_biginteger<B: BigInteger>(max: B, zero: B) {
    let mut rng = ark_std::test_rng();
    let a: B = UniformRand::rand(&mut rng);
    let b: B = UniformRand::rand(&mut rng);
    biginteger_arithmetic_test(a, b, zero, max);
    biginteger_bits_test::<B>();
    biginteger_conversion_test::<B>();
    biginteger_bitwise_ops_test::<B>();
    biginteger_shr::<B>();
    biginteger_shl::<B>();
}

#[test]
fn test_biginteger64() {
    use crate::biginteger::BigInteger64 as B;
    test_biginteger(B::new([u64::MAX; 1]), B::new([0u64; 1]));
}

#[test]
fn test_biginteger128() {
    use crate::biginteger::BigInteger128 as B;
    test_biginteger(B::new([u64::MAX; 2]), B::new([0u64; 2]));
}

#[test]
fn test_biginteger256() {
    use crate::biginteger::BigInteger256 as B;
    test_biginteger(B::new([u64::MAX; 4]), B::new([0u64; 4]));
}

#[test]
fn test_biginteger384() {
    use crate::biginteger::BigInteger384 as B;
    test_biginteger(B::new([u64::MAX; 6]), B::new([0u64; 6]));
}

#[test]
fn test_biginteger448() {
    use crate::biginteger::BigInteger448 as B;
    test_biginteger(B::new([u64::MAX; 7]), B::new([0u64; 7]));
}

#[test]
fn test_biginteger768() {
    use crate::biginteger::BigInteger768 as B;
    test_biginteger(B::new([u64::MAX; 12]), B::new([0u64; 12]));
}

#[test]
fn test_biginteger832() {
    use crate::biginteger::BigInteger832 as B;
    test_biginteger(B::new([u64::MAX; 13]), B::new([0u64; 13]));
}
