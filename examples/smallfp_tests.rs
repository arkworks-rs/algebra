use ark_algebra_test_templates::*;
use ark_ff::ark_ff_macros::SmallFpConfig;
use ark_ff::{BigInt, SmallFp, SmallFpConfig, SqrtPrecomputation};

#[derive(SmallFpConfig)]
#[modulus = "251"]
#[generator = "6"]
#[backend = "standard"]
pub struct SmallF8Config;
pub type SmallF8 = SmallFp<SmallF8Config>;

#[derive(SmallFpConfig)]
#[modulus = "251"]
#[generator = "6"]
#[backend = "montgomery"]
pub struct SmallF8ConfigMont;
pub type SmallF8Mont = SmallFp<SmallF8ConfigMont>;

#[derive(SmallFpConfig)]
#[modulus = "65521"]
#[generator = "2"]
#[backend = "standard"]
pub struct SmallF16Config;
pub type SmallF16 = SmallFp<SmallF16Config>;

#[derive(SmallFpConfig)]
#[modulus = "65521"]
#[generator = "2"]
#[backend = "montgomery"]
pub struct SmallF16ConfigMont;
pub type SmallF16Mont = SmallFp<SmallF16ConfigMont>;

#[derive(SmallFpConfig)]
#[modulus = "2147483647"] // m31
#[generator = "7"]
#[backend = "standard"]
pub struct SmallField;
pub type SmallF32 = SmallFp<SmallField>;

#[derive(SmallFpConfig)]
#[modulus = "2147483647"] // m31
#[generator = "7"]
#[backend = "montgomery"]
pub struct SmallFieldMont;
pub type SmallF32Mont = SmallFp<SmallFieldMont>;

#[derive(SmallFpConfig)]
#[modulus = "18446744069414584321"] // Goldilock's prime 2^64 - 2^32 + 1
#[generator = "2"]
#[backend = "standard"]
pub struct SmallF64Config;
pub type SmallF64 = SmallFp<SmallF64Config>;

#[derive(SmallFpConfig)]
#[modulus = "18446744069414584321"] // Goldilock's prime 2^64 - 2^32 + 1
#[generator = "2"]
#[backend = "montgomery"]
pub struct SmallF64ConfigMont;
pub type SmallF64Mont = SmallFp<SmallF64ConfigMont>;

#[derive(SmallFpConfig)]
#[modulus = "143244528689204659050391023439224324689"]
#[generator = "2"]
#[backend = "standard"]
pub struct SmallF128Config;
pub type SmallF128 = SmallFp<SmallF128Config>;

// #[derive(SmallFpConfig)]
// #[modulus = "143244528689204659050391023439224324689"]
// #[generator = "2"]
// #[backend = "montgomery"]
// pub struct SmallF128ConfigMont;
// pub type SmallF128Mont = SmallFp<SmallF128ConfigMont>;

test_small_field!(f8; SmallF8; small_prime_field);
test_small_field!(f8_mont; SmallF8Mont; small_prime_field);
test_small_field!(f16; SmallF16; small_prime_field);
test_small_field!(f16_mont; SmallF16Mont; small_prime_field);
test_small_field!(f32; SmallF32; small_prime_field);
test_small_field!(f32_mont; SmallF32Mont; small_prime_field);
test_small_field!(f64; SmallF64; small_prime_field);
test_small_field!(f64_mont; SmallF64Mont; small_prime_field);
test_small_field!(f128; SmallF128; small_prime_field);
// test_small_field!(f128_mont; SmallF128Mont; small_prime_field);

fn main() {
    let mut a = SmallFieldMont::new(20);
    println!("{}", a);
    SmallFieldMont::exit(&mut a);
    println!("{}", a);
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---------- Standard backend tests (existing) ----------
    #[test]
    fn add_assign_test() {
        let mut a = SmallField::new(20);
        let b = SmallField::new(10);
        let c = SmallField::new(30);
        a += b;
        assert_eq!(a.value, c.value);

        let mut a = SmallField::new(SmallField::MODULUS - 1);
        let b = SmallField::new(2);
        a += b;
        assert_eq!(a.value, 1);

        // adding zero
        let mut a = SmallField::new(42);
        let b = SmallField::ZERO;
        a += b;
        assert_eq!(a.value, 42);

        // max values
        let mut a = SmallField::new(SmallField::MODULUS - 1);
        let b = SmallField::new(SmallField::MODULUS - 1);
        a += b;
        assert_eq!(a.value, SmallField::MODULUS - 2);

        // adding one to maximum
        let mut a = SmallField::new(SmallField::MODULUS - 1);
        let b = SmallField::ONE;
        a += b;
        assert_eq!(a.value, 0);
    }

    #[test]
    fn sub_assign_test() {
        let mut a = SmallField::new(30);
        let b = SmallField::new(10);
        let c = SmallField::new(20);
        a -= b;
        assert_eq!(a.value, c.value);

        let mut a = SmallField::new(5);
        let b = SmallField::new(10);
        a -= b;
        assert_eq!(a.value, SmallField::MODULUS - 5);

        // subtracting zero
        let mut a = SmallField::new(42);
        let b = SmallField::ZERO;
        a -= b;
        assert_eq!(a.value, 42);

        // subtracting from zero
        let mut a = SmallField::ZERO;
        let b = SmallField::new(1);
        a -= b;
        assert_eq!(a.value, SmallField::MODULUS - 1);

        // self subtraction
        let mut a = SmallField::new(42);
        let b = SmallField::new(42);
        a -= b;
        assert_eq!(a.value, 0);

        // maximum minus one
        let mut a = SmallField::new(SmallField::MODULUS - 1);
        let b = SmallField::ONE;
        a -= b;
        assert_eq!(a.value, SmallField::MODULUS - 2);
    }

    #[test]
    fn mul_assign_test() {
        let mut a = SmallField::new(5);
        let b = SmallField::new(10);
        let c = SmallField::new(50);
        a *= b;
        assert_eq!(a.value, c.value);

        let mut a = SmallField::new(SmallField::MODULUS / 2);
        let b = SmallField::new(3);
        a *= b;
        assert_eq!(a.value, (SmallField::MODULUS / 2) * 3 % SmallField::MODULUS);

        // multiply by zero
        let mut a = SmallField::new(42);
        let b = SmallField::ZERO;
        a *= b;
        assert_eq!(a.value, 0);

        // multiply by one
        let mut a = SmallField::new(42);
        let b = SmallField::ONE;
        a *= b;
        assert_eq!(a.value, 42);

        // maximum values
        let mut a = SmallField::new(SmallField::MODULUS - 1);
        let b = SmallField::new(SmallField::MODULUS - 1);
        a *= b;
        assert_eq!(a.value, 1); // (p-1)*(p-1) = p^2 - 2p + 1 ≡ 1 (mod p)
    }

    #[test]
    fn neg_in_place_test() {
        let mut a = SmallField::new(10);
        SmallField::neg_in_place(&mut a);
        assert_eq!(a.value, SmallField::MODULUS - 10);

        let mut a = SmallField::ZERO;
        SmallField::neg_in_place(&mut a);
        assert_eq!(a.value, 0);

        // negate maximum
        let mut a = SmallField::new(SmallField::MODULUS - 1);
        SmallField::neg_in_place(&mut a);
        assert_eq!(a.value, 1);

        // Edge double negation
        let mut a = SmallField::new(42);
        let original = a.value;
        SmallField::neg_in_place(&mut a);
        SmallField::neg_in_place(&mut a);
        assert_eq!(a.value, original);

        // negate one
        let mut a = SmallField::ONE;
        SmallField::neg_in_place(&mut a);
        assert_eq!(a.value, SmallField::MODULUS - 1);
    }

    #[test]
    fn double_in_place_test() {
        let mut a = SmallField::new(10);
        SmallField::double_in_place(&mut a);
        assert_eq!(a.value, 20);

        let mut a = SmallField::new(SmallField::MODULUS - 1);
        SmallField::double_in_place(&mut a);
        assert_eq!(a.value, SmallField::MODULUS - 2);

        // double zero
        let mut a = SmallField::ZERO;
        SmallField::double_in_place(&mut a);
        assert_eq!(a.value, 0);

        // double maximum/2 + 1 (should wrap)
        if SmallField::MODULUS > 2 {
            let mut a = SmallField::new(SmallField::MODULUS / 2 + 1);
            SmallField::double_in_place(&mut a);
            assert_eq!(
                a.value,
                (SmallField::MODULUS / 2 + 1) * 2 % SmallField::MODULUS
            );
        }

        // double one
        let mut a = SmallField::ONE;
        SmallField::double_in_place(&mut a);
        assert_eq!(a.value, 2);
    }

    #[test]
    fn square_in_place_test() {
        let mut a = SmallField::new(5);
        let b = SmallField::new(25);
        SmallField::square_in_place(&mut a);
        assert_eq!(a.value, b.value);

        let mut a = SmallField::new(SmallField::MODULUS - 1);
        SmallField::square_in_place(&mut a);
        assert_eq!(a.value, 1);

        // square zero
        let mut a = SmallField::ZERO;
        SmallField::square_in_place(&mut a);
        assert_eq!(a.value, 0);

        // square one
        let mut a = SmallField::ONE;
        SmallField::square_in_place(&mut a);
        assert_eq!(a.value, 1);
    }

    #[test]
    fn zero_inverse() {
        let zero = SmallField::ZERO;
        assert!(SmallField::inverse(&zero).is_none())
    }

    #[test]
    fn test_specific_inverse() {
        let mut val = SmallField::new(17);
        let val_inv = SmallField::inverse(&val);
        SmallField::mul_assign(&mut val, &val_inv.unwrap());
        assert_eq!(val, SmallField::ONE);
    }

    #[test]
    fn test_inverse() {
        // inverse of 1
        let one = SmallField::ONE;
        let one_inv = SmallField::inverse(&one).unwrap();
        assert_eq!(one_inv, SmallField::ONE);

        // inverse of p-1 (which should be p-1 since (p-1)^2 ≡ 1 mod p)
        let neg_one = SmallField::new(SmallField::MODULUS - 1);
        let neg_one_inv = SmallField::inverse(&neg_one).unwrap();
        assert_eq!(neg_one_inv.value, SmallField::MODULUS - 1);

        for i in 1..100 {
            let val = SmallField::new(i);
            if let Some(inv) = SmallField::inverse(&val) {
                let mut product = val;
                SmallField::mul_assign(&mut product, &inv);
                assert_eq!(product, SmallField::ONE, "Failed for value {}", i);
            }
        }

        // inverse property: inv(inv(x)) = x
        let test_val = SmallField::new(42 % SmallField::MODULUS);
        if test_val.value != 0 {
            let inv1 = SmallField::inverse(&test_val).unwrap();
            let inv2 = SmallField::inverse(&inv1).unwrap();
            assert_eq!(test_val, inv2);
        }

        // inverse is multiplicative: inv(ab) = inv(a) * inv(b)
        let a = SmallField::new(7 % SmallField::MODULUS);
        let b = SmallField::new(11 % SmallField::MODULUS);
        if a.value != 0 && b.value != 0 {
            let mut ab = a;
            SmallField::mul_assign(&mut ab, &b);

            let inv_ab = SmallField::inverse(&ab).unwrap();
            let inv_a = SmallField::inverse(&a).unwrap();
            let inv_b = SmallField::inverse(&b).unwrap();

            let mut inv_a_times_inv_b = inv_a;
            SmallField::mul_assign(&mut inv_a_times_inv_b, &inv_b);

            assert_eq!(inv_ab, inv_a_times_inv_b);
        }
    }

    #[test]
    fn test_field_axioms() {
        // Test additive identity
        let a = SmallField::new(42 % SmallField::MODULUS);
        let b = SmallField::new(73 % SmallField::MODULUS);
        // commutativity of multiplication
        let mut a_times_b = a;
        let mut b_times_a = b;
        SmallField::mul_assign(&mut a_times_b, &b);
        SmallField::mul_assign(&mut b_times_a, &a);
        assert_eq!(a_times_b, b_times_a);

        // associativity of addition: (a + b) + c = a + (b + c)
        let c = SmallField::new(91 % SmallField::MODULUS);
        let mut ab_plus_c = a;
        SmallField::add_assign(&mut ab_plus_c, &b);
        SmallField::add_assign(&mut ab_plus_c, &c);

        let mut a_plus_bc = a;
        let mut bc = b;
        SmallField::add_assign(&mut bc, &c);
        SmallField::add_assign(&mut a_plus_bc, &bc);

        assert_eq!(ab_plus_c, a_plus_bc);

        // distributivity: a * (b + c) = a * b + a * c
        let mut a_times_bc = a;
        let mut bc = b;
        SmallField::add_assign(&mut bc, &c);
        SmallField::mul_assign(&mut a_times_bc, &bc);

        let mut ab_plus_ac = a;
        SmallField::mul_assign(&mut ab_plus_ac, &b);
        let mut ac = a;
        SmallField::mul_assign(&mut ac, &c);
        SmallField::add_assign(&mut ab_plus_ac, &ac);

        assert_eq!(a_times_bc, ab_plus_ac);
    }

    #[test]
    fn test_sum_of_products() {
        let a = [SmallField::new(2), SmallField::new(3), SmallField::new(5)];
        let b = [SmallField::new(7), SmallField::new(11), SmallField::new(13)];
        let result = SmallField::sum_of_products(&a, &b);
        assert_eq!(result.value, 112 % SmallField::MODULUS);

        let a = [SmallField::ZERO, SmallField::new(3), SmallField::ZERO];
        let b = [SmallField::new(7), SmallField::new(11), SmallField::new(13)];
        let result = SmallField::sum_of_products(&a, &b);
        assert_eq!(result.value, 33 % SmallField::MODULUS);
    }

    #[test]
    fn test_sqrt_standard_backend() {
        use ark_ff::Field;

        for i in [4, 16, 144, 169, 256, 400] {
            let a = SmallField::new(i);
            let sqrt = a.sqrt();
            assert!(sqrt.is_some());
            let sqrt_val = sqrt.unwrap();
            let mut sqrt_squared = sqrt_val;
            SmallField::square_in_place(&mut sqrt_squared);
            assert_eq!(sqrt_squared.value, i);
        }

        let three = SmallField::new(3);
        let sqrt_three = three.sqrt();
        assert!(sqrt_three.is_none());

        let one = SmallField::ONE;
        let sqrt_one = one.sqrt();
        assert!(sqrt_one.is_some());
        assert_eq!(sqrt_one.unwrap(), SmallField::ONE);

        let zero = SmallField::ZERO;
        let sqrt_zero = zero.sqrt();
        assert!(sqrt_zero.is_some());
        assert_eq!(sqrt_zero.unwrap(), SmallField::ZERO);
    }

    // ---------- Montgomery backend tests ----------
    #[test]
    fn add_assign_test_montgomery() {
        let mut a = SmallFieldMont::new(20);
        let b = SmallFieldMont::new(10);
        let mut c = SmallFieldMont::new(30);
        a += b;
        SmallFieldMont::exit(&mut a);
        SmallFieldMont::exit(&mut c);
        assert_eq!(a.value, c.value);

        let mut a = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        let b = SmallFieldMont::new(2);
        a += b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 1);

        // adding zero
        let mut a = SmallFieldMont::new(42);
        let b = SmallFieldMont::ZERO;
        a += b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 42);

        // max values
        let mut a = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        let b = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        a += b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, SmallFieldMont::MODULUS - 2);

        // adding one to maximum
        let mut a = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        let b = SmallFieldMont::ONE;
        a += b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 0);
    }

    #[test]
    fn sub_assign_test_montgomery() {
        let mut a = SmallFieldMont::new(30);
        let b = SmallFieldMont::new(10);
        let mut c = SmallFieldMont::new(20);
        a -= b;
        SmallFieldMont::exit(&mut a);
        SmallFieldMont::exit(&mut c);
        assert_eq!(a.value, c.value);

        let mut a = SmallFieldMont::new(5);
        let b = SmallFieldMont::new(10);
        a -= b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, SmallFieldMont::MODULUS - 5);

        // subtracting zero
        let mut a = SmallFieldMont::new(42);
        let b = SmallFieldMont::ZERO;
        a -= b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 42);

        // subtracting from zero
        let mut a = SmallFieldMont::ZERO;
        let b = SmallFieldMont::new(1);
        a -= b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, SmallFieldMont::MODULUS - 1);

        // self subtraction
        let mut a = SmallFieldMont::new(42);
        let b = SmallFieldMont::new(42);
        a -= b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 0);

        // maximum minus one
        let mut a = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        let b = SmallFieldMont::ONE;
        a -= b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, SmallFieldMont::MODULUS - 2);
    }

    #[test]
    fn mul_assign_test_montgomery() {
        let mut a = SmallFieldMont::new(5);
        let b = SmallFieldMont::new(10);
        let mut c = SmallFieldMont::new(50);
        a *= b;
        SmallFieldMont::exit(&mut a);
        SmallFieldMont::exit(&mut c);
        assert_eq!(a.value, c.value);

        let mut a = SmallFieldMont::new(SmallFieldMont::MODULUS / 2);
        let b = SmallFieldMont::new(3);
        a *= b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(
            a.value,
            (SmallFieldMont::MODULUS / 2) * 3 % SmallFieldMont::MODULUS
        );

        // multiply by zero
        let mut a = SmallFieldMont::new(42);
        let b = SmallFieldMont::ZERO;
        a *= b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 0);

        // multiply by one
        let mut a = SmallFieldMont::new(42);
        let b = SmallFieldMont::ONE;
        a *= b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 42);

        // maximum values
        let mut a = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        let b = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        a *= b;
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 1); // (p-1)*(p-1) ≡ 1 (mod p)
    }

    #[test]
    fn neg_in_place_test_montgomery() {
        let mut a = SmallFieldMont::new(10);
        SmallFieldMont::neg_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, SmallFieldMont::MODULUS - 10);

        let mut a = SmallFieldMont::ZERO;
        SmallFieldMont::neg_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 0);

        // negate maximum
        let mut a = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        SmallFieldMont::neg_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 1);

        // Edge double negation
        let mut a = SmallFieldMont::new(42);
        let original = {
            let mut tmp = a;
            SmallFieldMont::exit(&mut tmp);
            tmp.value
        };
        SmallFieldMont::neg_in_place(&mut a);
        SmallFieldMont::neg_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, original);

        // negate one
        let mut a = SmallFieldMont::ONE;
        SmallFieldMont::neg_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, SmallFieldMont::MODULUS - 1);
    }

    #[test]
    fn double_in_place_test_montgomery() {
        let mut a = SmallFieldMont::new(10);
        SmallFieldMont::double_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 20);

        let mut a = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        SmallFieldMont::double_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, SmallFieldMont::MODULUS - 2);

        // double zero
        let mut a = SmallFieldMont::ZERO;
        SmallFieldMont::double_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 0);

        // double maximum/2 + 1 (should wrap)
        if SmallFieldMont::MODULUS > 2 {
            let mut a = SmallFieldMont::new(SmallFieldMont::MODULUS / 2 + 1);
            SmallFieldMont::double_in_place(&mut a);
            SmallFieldMont::exit(&mut a);
            assert_eq!(
                a.value,
                (SmallFieldMont::MODULUS / 2 + 1) * 2 % SmallFieldMont::MODULUS
            );
        }

        // double one
        let mut a = SmallFieldMont::ONE;
        SmallFieldMont::double_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 2);
    }

    #[test]
    fn square_in_place_test_montgomery() {
        let mut a = SmallFieldMont::new(5);
        let mut b = SmallFieldMont::new(25);
        SmallFieldMont::square_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        SmallFieldMont::exit(&mut b);
        assert_eq!(a.value, b.value);

        let mut a = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        SmallFieldMont::square_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 1);

        // square zero
        let mut a = SmallFieldMont::ZERO;
        SmallFieldMont::square_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 0);

        // square one
        let mut a = SmallFieldMont::ONE;
        SmallFieldMont::square_in_place(&mut a);
        SmallFieldMont::exit(&mut a);
        assert_eq!(a.value, 1);
    }

    #[test]
    fn zero_inverse_montgomery() {
        let zero = SmallFieldMont::ZERO;
        assert!(SmallFieldMont::inverse(&zero).is_none())
    }

    #[test]
    fn test_specific_inverse_montgomery() {
        let val = SmallFieldMont::new(17);
        let val_inv = SmallFieldMont::inverse(&val);
        let mut val_copy = val;
        SmallFieldMont::mul_assign(&mut val_copy, &val_inv.unwrap());
        SmallFieldMont::exit(&mut val_copy);
        assert_eq!(val_copy.value, 1);
    }

    #[test]
    fn test_inverse_montgomery() {
        // inverse of 1
        let one = SmallFieldMont::ONE;
        let one_inv = SmallFieldMont::inverse(&one).unwrap();
        let mut one_inv_copy = one_inv;
        SmallFieldMont::exit(&mut one_inv_copy);
        assert_eq!(one_inv_copy.value, 1);

        // inverse of p-1 (which should be p-1 since (p-1)^2 ≡ 1 mod p)
        let neg_one = SmallFieldMont::new(SmallFieldMont::MODULUS - 1);
        let neg_one_inv = SmallFieldMont::inverse(&neg_one).unwrap();
        let mut tmp = neg_one_inv;
        SmallFieldMont::exit(&mut tmp);
        assert_eq!(tmp.value, SmallFieldMont::MODULUS - 1);

        for i in 1..100 {
            let val = SmallFieldMont::new(i);
            if let Some(inv) = SmallFieldMont::inverse(&val) {
                let mut product = val;
                SmallFieldMont::mul_assign(&mut product, &inv);
                SmallFieldMont::exit(&mut product);
                assert_eq!(product.value, 1, "Failed for value {}", i);
            }
        }

        // inverse property: inv(inv(x)) = x
        let test_val = SmallFieldMont::new(42 % SmallFieldMont::MODULUS);
        {
            let mut tv_copy = test_val;
            SmallFieldMont::exit(&mut tv_copy);
            if tv_copy.value != 0 {
                let inv1 = SmallFieldMont::inverse(&test_val).unwrap();
                let inv2 = SmallFieldMont::inverse(&inv1).unwrap();
                let mut inv2_copy = inv2;
                SmallFieldMont::exit(&mut inv2_copy);
                let mut original_copy = test_val;
                SmallFieldMont::exit(&mut original_copy);
                assert_eq!(original_copy.value, inv2_copy.value);
            }
        }

        // inverse is multiplicative: inv(ab) = inv(a) * inv(b)
        let a = SmallFieldMont::new(7 % SmallFieldMont::MODULUS);
        let b = SmallFieldMont::new(11 % SmallFieldMont::MODULUS);
        {
            let mut a_copy = a;
            SmallFieldMont::exit(&mut a_copy);
            let mut b_copy = b;
            SmallFieldMont::exit(&mut b_copy);
            if a_copy.value != 0 && b_copy.value != 0 {
                let mut ab = a;
                SmallFieldMont::mul_assign(&mut ab, &b);

                let inv_ab = SmallFieldMont::inverse(&ab).unwrap();
                let inv_a = SmallFieldMont::inverse(&a).unwrap();
                let inv_b = SmallFieldMont::inverse(&b).unwrap();

                let mut inv_a_times_inv_b = inv_a;
                SmallFieldMont::mul_assign(&mut inv_a_times_inv_b, &inv_b);

                let mut tmp1 = inv_ab;
                let mut tmp2 = inv_a_times_inv_b;
                SmallFieldMont::exit(&mut tmp1);
                SmallFieldMont::exit(&mut tmp2);
                assert_eq!(tmp1.value, tmp2.value);
            }
        }
    }

    #[test]
    fn test_field_axioms_montgomery() {
        // Test additive identity
        let a = SmallFieldMont::new(42 % SmallFieldMont::MODULUS);
        let b = SmallFieldMont::new(73 % SmallFieldMont::MODULUS);
        // commutativity of multiplication
        let mut a_times_b = a;
        let mut b_times_a = b;
        SmallFieldMont::mul_assign(&mut a_times_b, &b);
        SmallFieldMont::mul_assign(&mut b_times_a, &a);
        SmallFieldMont::exit(&mut a_times_b);
        SmallFieldMont::exit(&mut b_times_a);
        assert_eq!(a_times_b.value, b_times_a.value);

        // associativity of addition: (a + b) + c = a + (b + c)
        let c = SmallFieldMont::new(91 % SmallFieldMont::MODULUS);
        let mut ab_plus_c = a;
        SmallFieldMont::add_assign(&mut ab_plus_c, &b);
        SmallFieldMont::add_assign(&mut ab_plus_c, &c);

        let mut a_plus_bc = a;
        let mut bc = b;
        SmallFieldMont::add_assign(&mut bc, &c);
        SmallFieldMont::add_assign(&mut a_plus_bc, &bc);

        SmallFieldMont::exit(&mut ab_plus_c);
        SmallFieldMont::exit(&mut a_plus_bc);
        assert_eq!(ab_plus_c.value, a_plus_bc.value);

        // distributivity: a * (b + c) = a * b + a * c
        let mut a_times_bc = a;
        let mut bc = b;
        SmallFieldMont::add_assign(&mut bc, &c);
        SmallFieldMont::mul_assign(&mut a_times_bc, &bc);

        let mut ab_plus_ac = a;
        SmallFieldMont::mul_assign(&mut ab_plus_ac, &b);
        let mut ac = a;
        SmallFieldMont::mul_assign(&mut ac, &c);
        SmallFieldMont::add_assign(&mut ab_plus_ac, &ac);

        SmallFieldMont::exit(&mut a_times_bc);
        SmallFieldMont::exit(&mut ab_plus_ac);
        assert_eq!(a_times_bc.value, ab_plus_ac.value);
    }

    #[test]
    fn test_sum_of_products_montgomery() {
        let a = [
            SmallFieldMont::new(2),
            SmallFieldMont::new(3),
            SmallFieldMont::new(5),
        ];
        let b = [
            SmallFieldMont::new(7),
            SmallFieldMont::new(11),
            SmallFieldMont::new(13),
        ];
        let mut result = SmallFieldMont::sum_of_products(&a, &b);
        SmallFieldMont::exit(&mut result);
        assert_eq!(result.value, 112 % SmallFieldMont::MODULUS);

        let a = [
            SmallFieldMont::ZERO,
            SmallFieldMont::new(3),
            SmallFieldMont::ZERO,
        ];
        let b = [
            SmallFieldMont::new(7),
            SmallFieldMont::new(11),
            SmallFieldMont::new(13),
        ];
        let mut result = SmallFieldMont::sum_of_products(&a, &b);
        SmallFieldMont::exit(&mut result);
        assert_eq!(result.value, 33 % SmallFieldMont::MODULUS);
    }

    #[test]
    fn test_sqrt_montgomery_backend() {
        use ark_ff::Field;

        for i in [4, 16, 144, 169, 256, 400] {
            let a = SmallFieldMont::new(i);
            let sqrt = a.sqrt();
            assert!(sqrt.is_some());
            let sqrt_val = sqrt.unwrap();
            let mut sqrt_squared = sqrt_val;
            SmallFieldMont::square_in_place(&mut sqrt_squared);
            let mut a_copy = a;
            SmallFieldMont::exit(&mut sqrt_squared);
            SmallFieldMont::exit(&mut a_copy);
            assert_eq!(sqrt_squared.value, a_copy.value);
        }

        let three = SmallFieldMont::new(31);
        let sqrt_three = three.sqrt();
        assert!(sqrt_three.is_none());

        let one = SmallFieldMont::ONE;
        let sqrt_one = one.sqrt();
        assert!(sqrt_one.is_some());
        let mut sqrt_one_val = sqrt_one.unwrap();
        SmallFieldMont::exit(&mut sqrt_one_val);
        assert_eq!(sqrt_one_val.value, 1);

        let zero = SmallFieldMont::ZERO;
        let sqrt_zero = zero.sqrt();
        assert!(sqrt_zero.is_some());
        let mut sqrt_zero_val = sqrt_zero.unwrap();
        SmallFieldMont::exit(&mut sqrt_zero_val);
        assert_eq!(sqrt_zero_val.value, 0);
    }
}
