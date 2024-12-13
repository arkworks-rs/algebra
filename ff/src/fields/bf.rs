use num_bigint::BigUint;
use num_traits::{Zero, One};

#[derive( Clone, PartialEq, Eq)]
pub struct BinaryFieldElement {
    value: BigUint,
}

impl BinaryFieldElement {
    // Constructor to create a new [`BinaryFieldElement`]
    pub fn new(value: BigUint) -> Self {
        Self { value }
    }

    // Method for addition in GF(2^k)
    pub fn add(&self, other: &Self) -> Self {
        // Addition in binary fields is done with XOR
        Self::new(&self.value ^ &other.value)
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
            half_pow.mul(&half_pow)
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



#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::ToBigUint;

    #[test]
    fn add_test() {
        let a = BinaryFieldElement::new(1u64.to_biguint().unwrap());
        let b = BinaryFieldElement::new(0u64.to_biguint().unwrap());
        let c = BinaryFieldElement::new(100u64.to_biguint().unwrap());

        // Test cases
        assert_eq!(a.add(&b), BinaryFieldElement::new(1u64.to_biguint().unwrap()));
        assert_eq!(a.add(&a), BinaryFieldElement::new(0u64.to_biguint().unwrap())); // 1 + 1 in GF(2) should be 0
        assert_eq!(a.add(&c), BinaryFieldElement::new(101u64.to_biguint().unwrap())); // 1 + 100 = 101 in binary (XOR)
        assert_eq!(b.add(&c), BinaryFieldElement::new(100u64.to_biguint().unwrap())); // 0 + 100 = 100
    }

    #[test]
    fn sub_test() {
        let a = BinaryFieldElement::new(1u64.to_biguint().unwrap());
        let b = BinaryFieldElement::new(100u64.to_biguint().unwrap());

        assert_eq!(a.sub(&b), BinaryFieldElement::new(101u64.to_biguint().unwrap())); // 1 - 100 in GF(2) should be 101 (same as add)
    }

    #[test]
    fn neg_test() {
        let a = BinaryFieldElement::new(15u64.to_biguint().unwrap());
        assert_eq!(a.neg(), a); // Negation in GF(2) has no effect, so a == -a
    }

    #[test]
    fn multiplication_test() {
        let a = BinaryFieldElement::new(7u64.to_biguint().unwrap());
        let b = BinaryFieldElement::new(13u64.to_biguint().unwrap());
        assert_eq!(a.mul(&b), BinaryFieldElement::new(8u64.to_biguint().unwrap())); // 7 * 13 = 8
    }

    #[test]
    fn exponentiation_test() {
        let a = BinaryFieldElement::new(7u64.to_biguint().unwrap());
        assert_eq!(a.pow(3), BinaryFieldElement::new(4u64.to_biguint().unwrap())); // 7 ** 3 = 4
    }

    #[test]
    fn inverse_test() {
        let a = BinaryFieldElement::new(7u64.to_biguint().unwrap());
        assert_eq!(a.inv(), BinaryFieldElement::new(15u64.to_biguint().unwrap())); // Inverse of 7 = 15
    }

    #[test]
    fn division_test() {
        let a = BinaryFieldElement::new(7u64.to_biguint().unwrap());
        let b = BinaryFieldElement::new(13u64.to_biguint().unwrap());
        assert_eq!(a.div(&b), BinaryFieldElement::new(10u64.to_biguint().unwrap())); // 7 / 13 = 10
    }
}
