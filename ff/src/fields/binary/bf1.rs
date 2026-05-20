use crate::binary::small_unit::U1;
use ark_std::ops::Deref;
use ark_std::ops::{Add, AddAssign, Mul, MulAssign};
use ark_std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};

/// A binary field element represented using a single bit.
///
/// The [`Bf1`] type wraps a [`U1`] (1-bit unsigned integer) to represent binary field elements.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Bf1(U1);

impl Bf1 {
    /// Creates a new instance of [`Bf1`] from a [`U1`] value.
    pub const fn new(val: U1) -> Self {
        Self(val)
    }

    /// Returns the inner [`U1`] value of the [`Bf1`] element.
    pub fn inner(self) -> U1 {
        self.0
    }
}

impl Add for Bf1 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.0 ^ rhs.0)
    }
}

impl AddAssign for Bf1 {
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self.0 ^ rhs.0;
    }
}

impl Mul for Bf1 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.0 & rhs.0)
    }
}

impl MulAssign for Bf1 {
    fn mul_assign(&mut self, rhs: Self) {
        self.0 = self.0 & rhs.0;
    }
}

impl BitAnd for Bf1 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::new(self.0 & rhs.0)
    }
}

impl BitAndAssign for Bf1 {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 = self.0 & rhs.0;
    }
}

impl BitOr for Bf1 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::new(self.0 | rhs.0)
    }
}

impl BitOrAssign for Bf1 {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 = self.0 | rhs.0;
    }
}

impl BitXor for Bf1 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self::new(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for Bf1 {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 = self.0 ^ rhs.0;
    }
}

impl Deref for Bf1 {
    type Target = U1;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_addition() {
        let a = Bf1::new(U1::new(0));
        let b = Bf1::new(U1::new(1));
        assert_eq!(a + b, Bf1::new(U1::new(1)));

        let c = Bf1::new(U1::new(1));
        let d = Bf1::new(U1::new(1));
        assert_eq!(c + d, Bf1::new(U1::new(0)));

        let e = Bf1::new(U1::new(0));
        let f = Bf1::new(U1::new(0));
        assert_eq!(e + f, Bf1::new(U1::new(0)));
    }

    #[test]
    fn test_addition_assign() {
        let mut a = Bf1::new(U1::new(0));
        let b = Bf1::new(U1::new(1));
        a += b;
        assert_eq!(a, Bf1::new(U1::new(1)));

        let mut c = Bf1::new(U1::new(1));
        let d = Bf1::new(U1::new(1));
        c += d;
        assert_eq!(c, Bf1::new(U1::new(0)));

        let mut e = Bf1::new(U1::new(0));
        let f = Bf1::new(U1::new(0));
        e += f;
        assert_eq!(e, Bf1::new(U1::new(0)));
    }

    #[test]
    fn test_multiplication() {
        let a = Bf1::new(U1::new(1));
        let b = Bf1::new(U1::new(1));
        assert_eq!(a * b, Bf1::new(U1::new(1)));

        let c = Bf1::new(U1::new(1));
        let d = Bf1::new(U1::new(0));
        assert_eq!(c * d, Bf1::new(U1::new(0)));

        let e = Bf1::new(U1::new(0));
        let f = Bf1::new(U1::new(0));
        assert_eq!(e * f, Bf1::new(U1::new(0)));
    }

    #[test]
    fn test_multiplication_assign() {
        let mut a = Bf1::new(U1::new(1));
        let b = Bf1::new(U1::new(1));
        a *= b;
        assert_eq!(a, Bf1::new(U1::new(1)));

        let mut c = Bf1::new(U1::new(1));
        let d = Bf1::new(U1::new(0));
        c *= d;
        assert_eq!(c, Bf1::new(U1::new(0)));

        let mut e = Bf1::new(U1::new(0));
        let f = Bf1::new(U1::new(0));
        e *= f;
        assert_eq!(e, Bf1::new(U1::new(0)));
    }

    #[test]
    fn test_bitwise_and() {
        let a = Bf1::new(U1::new(1));
        let b = Bf1::new(U1::new(1));
        assert_eq!(a & b, Bf1::new(U1::new(1)));

        let c = Bf1::new(U1::new(1));
        let d = Bf1::new(U1::new(0));
        assert_eq!(c & d, Bf1::new(U1::new(0)));

        let e = Bf1::new(U1::new(0));
        let f = Bf1::new(U1::new(0));
        assert_eq!(e & f, Bf1::new(U1::new(0)));
    }

    #[test]
    fn test_bitwise_and_assign() {
        let mut a = Bf1::new(U1::new(1));
        let b = Bf1::new(U1::new(1));
        a &= b;
        assert_eq!(a, Bf1::new(U1::new(1)));

        let mut c = Bf1::new(U1::new(1));
        let d = Bf1::new(U1::new(0));
        c &= d;
        assert_eq!(c, Bf1::new(U1::new(0)));

        let mut e = Bf1::new(U1::new(0));
        let f = Bf1::new(U1::new(0));
        e &= f;
        assert_eq!(e, Bf1::new(U1::new(0)));
    }

    #[test]
    fn test_bitwise_or() {
        let a = Bf1::new(U1::new(1));
        let b = Bf1::new(U1::new(1));
        assert_eq!(a | b, Bf1::new(U1::new(1)));

        let c = Bf1::new(U1::new(1));
        let d = Bf1::new(U1::new(0));
        assert_eq!(c | d, Bf1::new(U1::new(1)));

        let e = Bf1::new(U1::new(0));
        let f = Bf1::new(U1::new(0));
        assert_eq!(e | f, Bf1::new(U1::new(0)));
    }

    #[test]
    fn test_bitwise_or_assign() {
        let mut a = Bf1::new(U1::new(1));
        let b = Bf1::new(U1::new(1));
        a |= b;
        assert_eq!(a, Bf1::new(U1::new(1)));

        let mut c = Bf1::new(U1::new(1));
        let d = Bf1::new(U1::new(0));
        c |= d;
        assert_eq!(c, Bf1::new(U1::new(1)));

        let mut e = Bf1::new(U1::new(0));
        let f = Bf1::new(U1::new(0));
        e |= f;
        assert_eq!(e, Bf1::new(U1::new(0)));
    }

    #[test]
    fn test_bitwise_xor() {
        let a = Bf1::new(U1::new(1));
        let b = Bf1::new(U1::new(1));
        assert_eq!(a ^ b, Bf1::new(U1::new(0)));

        let c = Bf1::new(U1::new(1));
        let d = Bf1::new(U1::new(0));
        assert_eq!(c ^ d, Bf1::new(U1::new(1)));

        let e = Bf1::new(U1::new(0));
        let f = Bf1::new(U1::new(0));
        assert_eq!(e ^ f, Bf1::new(U1::new(0)));
    }

    #[test]
    fn test_bitwise_xor_assign() {
        let mut a = Bf1::new(U1::new(1));
        let b = Bf1::new(U1::new(1));
        a ^= b;
        assert_eq!(a, Bf1::new(U1::new(0)));

        let mut c = Bf1::new(U1::new(1));
        let d = Bf1::new(U1::new(0));
        c ^= d;
        assert_eq!(c, Bf1::new(U1::new(1)));

        let mut e = Bf1::new(U1::new(0));
        let f = Bf1::new(U1::new(0));
        e ^= f;
        assert_eq!(e, Bf1::new(U1::new(0)));
    }
}
