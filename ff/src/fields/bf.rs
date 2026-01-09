use num_bigint::BigUint;
use num_traits::{Zero, One};
use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Div, DivAssign};


#[derive( Clone, PartialEq, Eq, Debug)]
pub struct BinaryFieldElement {
    value: BigUint,
}

impl BinaryFieldElement {
    // Constructor to create a new BinaryFieldElement
    pub fn new(value: BigUint) -> Self {
        BinaryFieldElement { value }
    }

    // Method for addition in GF(2^k)
    pub fn add(&self, other: &Self) -> Self {
        // Addition in binary fields is done with XOR
        BinaryFieldElement::new(&self.value ^ &other.value)
    }
    
    pub fn sub(&self, other: &Self) -> Self {
        self.add(other)
    }

    // Method for multiplication in GF(2^k)
    pub fn mul(&self, other: &Self) -> Self {
        BinaryFieldElement::new(binmul(self.value.clone(), other.value.clone(), None))
    }

    // Method for division (multiplication by the inverse)
    pub fn div(&self, other: &Self) -> Self {
        self.mul(&other.inv()) // Division as multiplication by inverse
    }

    pub fn neg(&self) -> Self {
        self.clone()
    }
    
    pub fn pow(&self, exponent: u64) -> Self {
        if exponent == 0 {
            BinaryFieldElement::new(BigUint::one())
        } else if exponent == 1 {
            self.clone()
        } else if exponent % 2 == 0 {
            let half_pow = self.pow(exponent / 2);
            half_pow.clone().mul(&half_pow)
        } else {
            self.mul(&self.pow(exponent - 1))
        }
    }

    // In a binary field GF(2^w) the inverse is a^{-1} = a^{2m-2}
    pub fn inv(&self) -> Self {
        let bit_len = self.value.bits();
        let l = 1 << (bit_len - 1).ilog2() + 1;
        return self.pow(2_u64.pow(l) - 2);
    }
}

// Binary field multiplication with reduction
fn binmul(v1: BigUint, v2: BigUint, length: Option<usize>) -> BigUint {
    if v1.is_zero() || v2.is_zero() {
        return BigUint::zero();
    }
    if v1.is_one() || v2.is_one() {
        return v1 * v2;
    }

    let length = length.unwrap_or_else(|| 1 << (v1.bits().max(v2.bits()) - 1).next_power_of_two());
    let halflen = length / 2;
    let quarterlen = halflen / 2;
    let halfmask = (BigUint::one() << halflen) - BigUint::one();

    let l1 = &v1 & &halfmask;
    let r1 = &v1 >> halflen;
    let l2 = &v2 & &halfmask;
    let r2 = &v2 >> halflen;

    // Optimized case for (L1, R1) == (0, 1)
    if l1.is_zero() && r1 == BigUint::one() {
        let out_r = binmul(BigUint::one() << quarterlen, r2.clone(), Some(halflen)) ^ l2.clone();
        return r2 ^ (out_r << halflen);
    }

    // Perform Karatsuba multiplication with three main sub-multiplications
    let l1l2 = binmul(l1.clone(), l2.clone(), Some(halflen));
    let r1r2 = binmul(r1.clone(), r2.clone(), Some(halflen));
    let r1r2_high = binmul(BigUint::one() << quarterlen, r1r2.clone(), Some(halflen));
    let z3 = binmul(l1 ^ r1.clone(), l2 ^ r2.clone(), Some(halflen));

    l1l2.clone() ^ r1r2.clone() ^ ((z3 ^ l1l2 ^ r1r2 ^ r1r2_high) << halflen)
}

// Implementations to be able to use +-*/
// Add implementations
impl<'a> AddAssign<&'a BinaryFieldElement> for BinaryFieldElement {
    #[inline]
    fn add_assign(&mut self, other: &'a BinaryFieldElement) {
        *self = BinaryFieldElement::add(self, other);
    }
}

impl<'a> Add<&'a BinaryFieldElement> for BinaryFieldElement {
    type Output = Self;

    #[inline]
    fn add(self, other: &'a Self) -> Self {
        BinaryFieldElement::add(&self, other)
    }
}

// Sub implementations
impl<'a> SubAssign<&'a BinaryFieldElement> for BinaryFieldElement {
    #[inline]
    fn sub_assign(&mut self, other: &'a BinaryFieldElement) {
        *self = BinaryFieldElement::sub(self, other);
    }
}

impl<'a> Sub<&'a BinaryFieldElement> for BinaryFieldElement {
    type Output = Self;

    #[inline]
    fn sub(self, other: &'a Self) -> Self {
        BinaryFieldElement::sub(&self, other)
    }
}

// Mul implementations
impl<'a> MulAssign<&'a BinaryFieldElement> for BinaryFieldElement {
    #[inline]
    fn mul_assign(&mut self, other: &'a BinaryFieldElement) {
        *self = BinaryFieldElement::mul(self, other);
    }
}

impl<'a> Mul<&'a BinaryFieldElement> for BinaryFieldElement {
    type Output = Self;

    #[inline]
    fn mul(self, other: &'a Self) -> Self {
        BinaryFieldElement::mul(&self, other)
    }
}

// Div implementations
impl<'a> DivAssign<&'a BinaryFieldElement> for BinaryFieldElement {
    #[inline]
    fn div_assign(&mut self, other: &'a BinaryFieldElement) {
        *self = BinaryFieldElement::div(self, other);
    }
}

impl<'a> Div<&'a BinaryFieldElement> for BinaryFieldElement {
    type Output = Self;

    #[inline]
    fn div(self, other: &'a Self) -> Self {
        BinaryFieldElement::div(&self, other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::ToBigUint;
    use ark_std::{test_rng, rand::RngCore};  // Changed to RngCore


    #[test]
    fn add_test() {
        let a = BinaryFieldElement::new(1u64.to_biguint().unwrap());
        let b = BinaryFieldElement::new(0u64.to_biguint().unwrap());
        let c = BinaryFieldElement::new(100u64.to_biguint().unwrap());

        // Test cases
        assert_eq!(a.clone().add(&b), BinaryFieldElement::new(1u64.to_biguint().unwrap()));
        assert_eq!(a.clone().add(&a), BinaryFieldElement::new(0u64.to_biguint().unwrap())); // 1 + 1 in GF(2) should be 0
        assert_eq!(a.clone().add(&c), BinaryFieldElement::new(101u64.to_biguint().unwrap())); // 1 + 100 = 101 in binary (XOR)
        assert_eq!(b.add(&c), BinaryFieldElement::new(100u64.to_biguint().unwrap())); // 0 + 100 = 100
    }

    #[test]
    fn sub_test() {
        let a = BinaryFieldElement::new(1u64.to_biguint().unwrap());
        let b = BinaryFieldElement::new(100u64.to_biguint().unwrap());

        assert_eq!(a.clone().sub(&b), BinaryFieldElement::new(101u64.to_biguint().unwrap())); // 1 - 100 in GF(2) should be 101 (same as add)
    }

    #[test]
    fn neg_test() {
        let a = BinaryFieldElement::new(15u64.to_biguint().unwrap());
        assert_eq!(a.clone().neg(), a); // Negation in GF(2) has no effect, so a == -a
    }

    #[test]
    fn multiplication_test() {
        let a = BinaryFieldElement::new(7u64.to_biguint().unwrap());
        let b = BinaryFieldElement::new(13u64.to_biguint().unwrap());
        assert_eq!(a.clone().mul(&b), BinaryFieldElement::new(8u64.to_biguint().unwrap())); // 7 * 13 = 8
    }

    #[test]
    fn exponentiation_test() {
        let a = BinaryFieldElement::new(7u64.to_biguint().unwrap());
        assert_eq!(a.clone().pow(3), BinaryFieldElement::new(4u64.to_biguint().unwrap())); // 7 ** 3 = 4
    }

    #[test]
    fn inverse_test() {
        let a = BinaryFieldElement::new(7u64.to_biguint().unwrap());
        assert_eq!(a.clone().inv(), BinaryFieldElement::new(15u64.to_biguint().unwrap())); // Inverse of 7 = 15
    }

    #[test]
    fn division_test() {
        let a = BinaryFieldElement::new(7u64.to_biguint().unwrap());
        let b = BinaryFieldElement::new(13u64.to_biguint().unwrap());
        assert_eq!(a.clone().div(&b), BinaryFieldElement::new(10u64.to_biguint().unwrap())); // 7 / 13 = 10
    }

    #[test]
    fn test_random_operations() {
        let mut rng = test_rng();

        // Generate some random values (using smaller numbers for testing)
        for _ in 0..100 {  // Run 100 random tests
            // Generate non-zero random values between 1 and 255
            let value1 = ((rng.next_u64() % 255) + 1).to_biguint().unwrap();
            let value2 = ((rng.next_u64() % 255) + 1).to_biguint().unwrap();    

            let a = BinaryFieldElement::new(value1.clone());
            let b = BinaryFieldElement::new(value2.clone());

            // Test that a + b = b + a (commutativity of addition)
            assert_eq!(a.clone().add(&b), b.clone().add(&a));

            // Test that (a + b) + c = a + (b + c) (associativity of addition)
            let c = BinaryFieldElement::new((rng.next_u64() % 256).to_biguint().unwrap());
            assert_eq!(
                a.clone().add(&b).add(&c),
                a.clone().add(&b.clone().add(&c))
            );

            // Test that a + 0 = a (identity of addition)
            let zero = BinaryFieldElement::new(0u64.to_biguint().unwrap());
            assert_eq!(a.clone().add(&zero), a.clone());

            // Test that a + a = 0 (characteristic 2)
            assert_eq!(a.clone().add(&a), zero);

            // Test multiplication properties
            assert_eq!(a.clone().mul(&b), b.clone().mul(&a));  // commutativity

            // Test that a * (b * c) = (a * b) * c (associativity of multiplication)
            assert_eq!(
                a.clone().mul(&b.clone().mul(&c)),
                a.clone().mul(&b).mul(&c)
            );

            // Test distributive property: a * (b + c) = (a * b) + (a * c)
            assert_eq!(
                a.clone().mul(&b.clone().add(&c)),
                a.clone().mul(&b).add(&a.clone().mul(&c))
            );

            // Test inverse (if not zero)
            if !a.value.is_zero() {
                let a_inv = a.clone().inv();
                assert_eq!(a.clone().mul(&a_inv), BinaryFieldElement::new(1u64.to_biguint().unwrap()));
            }
        }
    }
}
