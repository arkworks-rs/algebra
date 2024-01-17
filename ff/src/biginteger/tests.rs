use crate::{biginteger::BigInteger, UniformRand};
use num_bigint::BigUint;

// Test elementary math operations for BigInteger.
fn biginteger_arithmetic_test<B: BigInteger>(a: B, b: B, zero: B) {
    // zero == zero
    assert_eq!(zero, zero);

    // zero.is_zero() == true
    assert_eq!(zero.is_zero(), true);

    // one.is_one() == true
    let one = B::from(1u64);
    assert!(one.is_one());

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
    a_plus_a.add_with_carry(&a); // Won't assert anything about carry bit.
    assert_eq!(a_mul2, a_plus_a);
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

fn biginteger_modulus<B: BigInteger>() {
    let mut rng = ark_std::test_rng();

    // Basic tests
    let a = B::rand(&mut rng);
    assert_eq!(B::from(0u64) % a, B::from(0u64));
    assert_eq!(a % B::from(1u64), B::from(0u64));

    // Check that the modulus computation agrees with parity test.
    if a.is_even() {
        assert_eq!(a % B::from(2u64), B::from(0u64));
    } else {
        assert_eq!(a % B::from(2u64), B::from(1u64));
    }

    // Check modulus identity.
    let a = B::rand(&mut rng);
    let b = B::rand(&mut rng);
    let a_mod_b = a % b;
    let a_mod_b_mod_b = a_mod_b % b;
    assert_eq!(a_mod_b, a_mod_b_mod_b);

    // Check trivial cases from comparisons.
    let a = B::rand(&mut rng);
    let b = B::rand(&mut rng);
    match a.cmp(&b) {
        core::cmp::Ordering::Less => assert_eq!(a % b, a),
        core::cmp::Ordering::Equal => assert_eq!(a % b, B::from(0u64)),
        core::cmp::Ordering::Greater => {},
    }
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
    biginteger_bitwise_ops_test::<B>();
    biginteger_shr::<B>();
    biginteger_shl::<B>();
    biginteger_modulus::<B>();
}

#[test]
fn biginteger_modulus_static_tests() {
    use crate::biginteger::BigInt;

    let a64 = BigInt::new([3601073082870250418]);
    let b64 = BigInt::new([2193000201251463648]);
    let mod64 = BigInt::new([1408072881618786770]);
    assert_eq!(a64 % b64, mod64);

    let a128 = BigInt::new([4174451077990245596, 3669629040712867839]);
    let b128 = BigInt::new([8908506066818206150, 17331115722498298823]);
    let mod128 = BigInt::new([4174451077990245596, 3669629040712867839]);
    assert_eq!(a128 % b128, mod128);

    let a256 = BigInt::new([
        14621467787333493418,
        12108485322752294880,
        11620129110562858835,
        6771525239094520794,
    ]);
    let b256 = BigInt::new([
        9457583366609244046,
        3292446216252191244,
        15683190688725518430,
        12376509759692993049,
    ]);
    let mod256 = BigInt::new([
        14621467787333493418,
        12108485322752294880,
        11620129110562858835,
        6771525239094520794,
    ]);
    assert_eq!(a256 % b256, mod256);

    let a512 = BigInt::new([
        12510516664288822641,
        14513930181904105826,
        13449486877885219817,
        8005255619594419542,
        6228641990551128361,
        8770155517167400132,
        15617099880276166326,
        17143852322472171649,
    ]);
    let b512 = BigInt::new([
        14002016314341253844,
        18398549445620213883,
        5645345381311304630,
        16592555506467753304,
        16984857277391876626,
        16427282640994978259,
        11465536577168429635,
        698543981412520453,
    ]);
    let mod512 = BigInt::new([
        8503518446870659473,
        15670601256048211400,
        7088406242380769985,
        15612293085978475791,
        4420436954756224867,
        1896997681188505830,
        17145383133877129305,
        378796768571680762,
    ]);
    assert_eq!(a512 % b512, mod512);

    let a1024 = BigInt::new([
        813765468505266982,
        9461391675911782696,
        9082012781690260231,
        8393500664090969669,
        4133856364806303958,
        11149080897905582441,
        14731346490539363185,
        989680701211629440,
        8526880266768469178,
        2316258228357047461,
        5239140938378412139,
        13856807587119809799,
        17095289661235426508,
        15245639872422554895,
        15979549614507724819,
        1709763898347752414,
    ]);
    let b1024 = BigInt::new([
        14373198534555697120,
        1857962328286269016,
        15002453475225291270,
        12505120393686880765,
        17843441582302809739,
        8589716293423618750,
        684922508168804796,
        3583840145186657945,
        14969815686562072035,
        13969943195137168376,
        11597877104598378561,
        8138617899241207781,
        11747787798498493404,
        10447752210747488036,
        2262843315480796728,
        6590054619087534118,
    ]);
    let mod1024 = BigInt::new([
        813765468505266982,
        9461391675911782696,
        9082012781690260231,
        8393500664090969669,
        4133856364806303958,
        11149080897905582441,
        14731346490539363185,
        989680701211629440,
        8526880266768469178,
        2316258228357047461,
        5239140938378412139,
        13856807587119809799,
        17095289661235426508,
        15245639872422554895,
        15979549614507724819,
        1709763898347752414,
    ]);
    assert_eq!(a1024 % b1024, mod1024);
}

#[test]
fn test_from_two_u64_to_128() {
    use crate::biginteger::from_two_u64_to_u128;

    let mut rng = ark_std::test_rng();
    let a = u64::rand(&mut rng);
    let b = u64::rand(&mut rng);

    let r = from_two_u64_to_u128(a, b);

    let ref_val = (b as u128) * ((u64::MAX as u128) + 1) + (a as u128);
    assert_eq!(ref_val, r);
}

#[test]
fn test_conversion_u64_u128() {
    use crate::biginteger::{from_two_u64_to_u128, get_u64_limbs_from_u128};

    let mut rng = ark_std::test_rng();
    let a = u64::rand(&mut rng);
    let b = u64::rand(&mut rng);

    let r = from_two_u64_to_u128(a, b);

    let (b_hat, a_hat) = get_u64_limbs_from_u128(r);

    assert_eq!(a, a_hat);
    assert_eq!(b, b_hat);
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
