use crate::{biginteger::BigInteger, BigInt, UniformRand};
use ark_std::rand::Rng;
use num_bigint::BigUint;

// Test elementary math operations for BigInteger.
fn biginteger_arithmetic_test<B: BigInteger>(a: B, b: B, zero: B) {
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
    a_mul1.muln(0);
    assert_eq!(a_mul1, a);

    // a * 2 = a + a
    let mut a_mul2 = a;
    a_mul2.mul2();
    let mut a_plus_a = a;
    a_plus_a.add_with_carry(&a); // Won't assert anything about carry bit.
    assert_eq!(a_mul2, a_plus_a);
}

// Test for BigInt's bitwise operations
fn biginteger_bitwise_ops_test<B: BigInteger>() {
    let mut rng = ark_std::test_rng();

    // Test XOR
    // a xor a = 0
    let a: BigInt<4> = UniformRand::rand(&mut rng);
    assert_eq!(a ^ &a, BigInt::from(0_u64));

    // Testing a xor b xor b
    let a: BigInt<4> = UniformRand::rand(&mut rng);
    let b: BigInt<4> = UniformRand::rand(&mut rng);
    let xor_ab = a ^ b;
    assert_eq!(xor_ab ^ b, a);

    // Test OR
    // a or a = a
    let a = rng.gen::<BigInt<4>>();
    assert_eq!(a | &a, a);

    // Testing a or b or b
    let a = rng.gen::<BigInt<4>>();
    let b = rng.gen::<BigInt<4>>();
    let or_ab = a | b;
    assert_eq!(or_ab | &b, a | b);

    // Test AND
    // a and a = a
    let a = rng.gen::<BigInt<4>>();
    assert_eq!(a & (&a), a);

    // Testing a and a and b.
    let a = rng.gen::<BigInt<4>>();
    let b = rng.gen::<BigInt<4>>();
    let b_clone = b.clone();
    let and_ab = a & b;
    assert_eq!(and_ab & b_clone, a & b);

    // Testing De Morgan's law
    let a = rng.gen::<BigInt<4>>();
    let b = rng.gen::<BigInt<4>>();
    let de_morgan_lhs = !(a | b);
    let de_morgan_rhs = (!a) & (!b);
    assert_eq!(de_morgan_lhs, de_morgan_rhs);
}

// Test correctness of BigInteger's bit values
fn biginteger_bits_test<B: BigInteger>() {
    let mut one = B::from(1u64);
    // 0th bit of BigInteger representing 1 is 1
    assert!(one.get_bit(0));
    // 1st bit of BigInteger representing 1 is not 1
    assert!(!one.get_bit(1));
    one.muln(5);
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
fn test_biginteger<B: BigInteger>(zero: B) {
    let mut rng = ark_std::test_rng();
    let a: B = UniformRand::rand(&mut rng);
    let b: B = UniformRand::rand(&mut rng);
    biginteger_arithmetic_test(a, b, zero);
    biginteger_bits_test::<B>();
    biginteger_conversion_test::<B>();
    biginteger_bitwise_ops_test::<B>()
}

#[test]
fn test_biginteger64() {
    use crate::biginteger::BigInteger64 as B;
    test_biginteger(B::new([0u64; 1]));
}

#[test]
fn test_biginteger128() {
    use crate::biginteger::BigInteger128 as B;
    test_biginteger(B::new([0u64; 2]));
}

#[test]
fn test_biginteger256() {
    use crate::biginteger::BigInteger256 as B;
    test_biginteger(B::new([0u64; 4]));
}

#[test]
fn test_biginteger384() {
    use crate::biginteger::BigInteger384 as B;
    test_biginteger(B::new([0u64; 6]));
}

#[test]
fn test_biginteger448() {
    use crate::biginteger::BigInteger448 as B;
    test_biginteger(B::new([0u64; 7]));
}

#[test]
fn test_biginteger768() {
    use crate::biginteger::BigInteger768 as B;
    test_biginteger(B::new([0u64; 12]));
}

#[test]
fn test_biginteger832() {
    use crate::biginteger::BigInteger832 as B;
    test_biginteger(B::new([0u64; 13]));
}
