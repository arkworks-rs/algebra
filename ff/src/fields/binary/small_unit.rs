// Derived from work licensed under the Apache License 2.0
// Copyright 2024 Irreducible Inc.

use ark_std::ops::Deref;
use ark_std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};

/// Represents an unsigned integer type with a bit-width of `N`.
///
/// This type wraps a `u8` value and ensures that only the least significant `N` bits are valid.
/// Any operations performed will respect the constraints imposed by the bit-width `N`.
///
/// # Type Parameters
/// - `N`: The number of bits in the type. Must be strictly less than 8.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SmallU<const N: usize>(u8);

impl<const N: usize> SmallU<N> {
    /// Represents the zero value for this type.
    ///
    /// All bits are cleared (set to `0`).
    pub const ZERO: Self = Self(0);

    /// Represents the one value for this type.
    ///
    /// Only the least significant bit is set to `1`.
    pub const ONE: Self = Self(1);

    /// A constant representing the maximum possible value for the [`SmallU`] type,
    /// where all `N` least significant bits are set to `1`.
    ///
    /// For example:
    /// - If `N = 3`, the value is `0b00000111` (decimal `7`).
    /// - If `N = 1`, the value is `0b00000001` (decimal `1`).
    pub const MAX: Self = Self((1u8 << N) - 1);

    /// Creates a new instance of [`SmallU`] with the given value.
    ///
    /// The value is masked so that only the least significant `N` bits are retained.
    ///
    /// # Parameters
    /// - `val`: The input value to initialize the instance.
    ///
    /// # Returns
    /// A new [`SmallU`] instance where only the least significant `N` bits are valid.
    pub const fn new(val: u8) -> Self {
        // Mask the input value with the maximum possible value (`MAX`)
        // to retain only the least significant `N` bits.
        Self(val & Self::MAX.0)
    }

    /// Creates a new instance of [`SmallU`] without applying bit-width constraints.
    ///
    /// This method does not mask the input value and directly assigns it to the internal field.
    /// Use this method only when the input value is guaranteed to be valid for the specified
    /// bit-width `N`, as this bypasses the safety check provided by the `new` method.
    ///
    /// # Parameters
    /// - `val`: The input value to initialize the instance.
    ///
    /// # Returns
    /// A new [`SmallU`] instance with the raw input value.
    ///
    /// # Safety
    /// It is the caller's responsibility to ensure the input value respects the `N` bit-width.
    pub const fn new_unchecked(val: u8) -> Self {
        Self(val)
    }
}

impl<const N: usize> BitAnd for SmallU<N> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::new_unchecked(self.0 & rhs.0)
    }
}

impl<const N: usize> BitAndAssign for SmallU<N> {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

impl<const N: usize> BitOr for SmallU<N> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::new_unchecked(self.0 | rhs.0)
    }
}

impl<const N: usize> BitOrAssign for SmallU<N> {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl<const N: usize> BitXor for SmallU<N> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self::new_unchecked(self.0 ^ rhs.0)
    }
}

impl<const N: usize> BitXorAssign for SmallU<N> {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl<const N: usize> Deref for SmallU<N> {
    type Target = u8;

    /// Returns a reference to the inner `u8` value.
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A concrete instantiation of [`SmallU`] with a 1-bit width.
///
/// This type allows only the values `0` and `1`.
pub type U1 = SmallU<1>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u1_initialization() {
        // Test U1 values
        assert_eq!(U1::new(0), U1::ZERO);
        assert_eq!(U1::new(1), U1::ONE);

        // Should wrap around to 0 due to bit masking
        assert_eq!(U1::new(2), U1::ZERO);
    }

    #[test]
    fn test_u1_bitwise_operations() {
        // Initialize U1 values.
        let a = U1::new(0);
        let b = U1::new(1);

        // Test bitwise AND operation.
        // 0 AND 1 = 0.
        assert_eq!(a & b, U1::new(0));
        // Test bitwise OR operation.
        // 0 OR 1 = 1.
        assert_eq!(a | b, U1::new(1));
        // Test bitwise XOR operation.
        // 0 XOR 1 = 1.
        assert_eq!(a ^ b, U1::new(1));

        // Repeat tests where both operands are `b` (value 1).
        // 1 AND 1 = 1.
        assert_eq!(b & b, U1::new(1));
        // 1 OR 1 = 1.
        assert_eq!(b | b, U1::new(1));
        // 1 XOR 1 = 0.
        assert_eq!(b ^ b, U1::new(0));

        // Repeat tests where both operands are `a` (value 0).
        // 0 AND 0 = 0.
        assert_eq!(a & a, U1::new(0));
        // 0 OR 0 = 0.
        assert_eq!(a | a, U1::new(0));
        // 0 XOR 0 = 0.
        assert_eq!(a ^ a, U1::new(0));
    }

    #[test]
    fn test_u1_constants() {
        // `U1::ZERO` is defined as the U1 representation of 0.
        assert_eq!(U1::ZERO, U1::new(0));

        // `U1::ONE` is defined as the U1 representation of 1.
        assert_eq!(U1::ONE, U1::new(1));

        // In a U1 type, `MAX` represents all bits set, which is equivalent to 1 since only one bit
        // is allowed.
        assert_eq!(U1::MAX, U1::new(1));
    }

    #[test]
    fn test_u1_overflow() {
        // Should wrap around to 0
        assert_eq!(U1::new(2), U1::new(0));
        // Should wrap around to 1
        assert_eq!(U1::new(3), U1::new(1));
    }

    #[test]
    fn test_u1_equality_and_ordering() {
        // Create a U1 instance `a` with the value 0.
        let a = U1::new(0);

        // Create another U1 instance `b` with the value 1.
        let b = U1::new(1);

        // Check that `a` is less than `b`.
        // This verifies the `<` operator implementation for U1.
        assert!(a < b);

        // Check that `b` is greater than `a`.
        // This verifies the `>` operator implementation for U1.
        assert!(b > a);
    }

    #[test]
    fn test_bitwise_operations() {
        let a = U1::new(0);
        let b = U1::new(1);

        // Bitwise AND
        assert_eq!(a & b, U1::new(0));
        assert_eq!(b & b, U1::new(1));

        // Bitwise OR
        assert_eq!(a | b, U1::new(1));
        assert_eq!(b | b, U1::new(1));

        // Bitwise XOR
        assert_eq!(a ^ b, U1::new(1));
        assert_eq!(b ^ b, U1::new(0));

        let mut c = U1::new(1);
        c &= U1::new(0);
        assert_eq!(c, U1::new(0));

        let mut d = U1::new(0);
        d |= U1::new(1);
        assert_eq!(d, U1::new(1));

        let mut e = U1::new(1);
        e ^= U1::new(1);
        assert_eq!(e, U1::new(0));
    }

    #[test]
    fn test_non_zero_one_bitwise_operations() {
        let a = U1::new(3); // 3 wraps to 1
        let b = U1::new(2); // 2 wraps to 0

        // Bitwise AND
        assert_eq!(a & b, U1::new(0));

        // Bitwise OR
        assert_eq!(a | b, U1::new(1));

        // Bitwise XOR
        assert_eq!(a ^ b, U1::new(1));

        let mut c = U1::new(3);
        c &= U1::new(2);
        assert_eq!(c, U1::new(0));

        let mut d = U1::new(2);
        d |= U1::new(3);
        assert_eq!(d, U1::new(1));

        let mut e = U1::new(3);
        e ^= U1::new(2);
        assert_eq!(e, U1::new(1));
    }
}
