use ark_std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{AdditiveGroup, MultiplicativeGroup, PrimeField};

mod scalar;
use scalar::Scalar as Sc;
pub use scalar::{Scalar, Sign};

pub trait ScalarMul<Scalar: Sc>:
    AdditiveGroup
    + 'static
    + Mul<Scalar, Output = Self>
    + for<'a> Mul<&'a Scalar, Output = Self>
    + for<'a> Mul<&'a mut Scalar, Output = Self>
    + MulAssign<Scalar>
    + for<'a> MulAssign<&'a Scalar>
    + for<'a> MulAssign<&'a mut Scalar>
    + Add<Self::MulBase, Output = Self>
    + AddAssign<Self::MulBase>
    + for<'a> Add<&'a Self::MulBase, Output = Self>
    + for<'a> AddAssign<&'a Self::MulBase>
    + Sub<Self::MulBase, Output = Self>
    + SubAssign<Self::MulBase>
    + for<'a> Sub<&'a Self::MulBase, Output = Self>
    + for<'a> SubAssign<&'a Self::MulBase>
    + From<Self::MulBase>
{
    type MulBase: Send
        + Sync
        + Copy
        + Eq
        + core::hash::Hash
        + Mul<Scalar, Output = Self>
        + for<'a> Mul<&'a Scalar, Output = Self>
        + Neg<Output = Self::MulBase>
        + From<Self>;

    const NEGATION_IS_CHEAP: bool;

    fn batch_convert_to_mul_base(bases: &[Self]) -> Vec<Self::MulBase>;
}

pub trait ScalarExp<Exponent: Sc>:
    MultiplicativeGroup
    + Mul<Self::ExpBase, Output = Self>
    + MulAssign<Self::ExpBase>
    + for<'a> Mul<&'a Self::ExpBase, Output = Self>
    + for<'a> MulAssign<&'a Self::ExpBase>
    + Div<Self::ExpBase, Output = Self>
    + DivAssign<Self::ExpBase>
    + for<'a> Div<&'a Self::ExpBase, Output = Self>
    + for<'a> DivAssign<&'a Self::ExpBase>
    + From<Self::ExpBase>
{
    type ExpBase: Send + Sync + Copy + Eq + core::hash::Hash;

    const INVERSION_IS_FAST: bool;

    /// Returns `self^exp`, where `exp` is a scalar.
    #[must_use]
    fn pow(&self, exp: Exponent) -> Self {
        let mut res = Self::one();
        let (sign, exp) = exp.as_u64s();

        for i in crate::bits::BitIteratorBE::without_leading_zeros(exp) {
            res.square_in_place();

            if i {
                res *= self;
            }
        }
        if sign.is_negative() {
            res.invert_in_place();
        }
        res
    }

    /// Exponentiates an element `f` by a number represented with `u64`
    /// limbs, using a precomputed table containing as many powers of 2 of
    /// `f` as the 1 + the floor of log2 of the exponent `exp`, starting
    /// from the 1st power. That is, `powers_of_2` should equal `&[p, p^2,
    /// p^4, ..., p^(2^n)]` when `exp` has at most `n` bits.
    ///
    /// This returns `None` when a power is missing from the table.
    #[must_use]
    fn pow_with_table(powers_of_2: &[Self], exp: Exponent) -> Option<Self> {
        let mut res = Self::one();
        let (sign, exp) = exp.as_u64s();
        for (pow, bit) in crate::bits::BitIteratorLE::without_trailing_zeros(exp).enumerate() {
            if bit {
                res *= powers_of_2.get(pow)?;
            }
        }
        if sign.is_negative() {
            res.invert_in_place();
        }
        Some(res)
    }

    /// Returns `self^exp`, where `exp` is a scalar.
    #[must_use]
    fn pow_exp_base(base: &Self::ExpBase, exp: Exponent) -> Self {
        let mut res = Self::one();
        let (sign, exp) = exp.as_u64s();
        for (i, bit) in crate::bits::BitIteratorBE::without_leading_zeros(exp).enumerate() {
            res.square_in_place();
            if bit {
                res *= base;
            }
        }
        if sign.is_negative() {
            res.invert_in_place();
        }
        res
    }

    /// Exponentiates a field element `f` by a number represented with `u64`
    /// limbs, using a precomputed table containing as many powers of 2 of
    /// `f` as the 1 + the floor of log2 of the exponent `exp`, starting
    /// from the 1st power. That is, `powers_of_2` should equal `&[p, p^2,
    /// p^4, ..., p^(2^n)]` when `exp` has at most `n` bits.
    ///
    /// This returns `None` when a power is missing from the table.
    #[must_use]
    fn pow_exp_base_with_table(powers_of_2: &[Self::ExpBase], exp: Exponent) -> Option<Self> {
        let mut res = Self::one();
        let (sign, exp) = exp.as_u64s();
        for (pow, bit) in crate::bits::BitIteratorLE::without_trailing_zeros(exp).enumerate() {
            if bit {
                res *= powers_of_2.get(pow)?;
            }
        }
        if sign.is_negative() {
            res.invert_in_place();
        }
        Some(res)
    }

    fn batch_convert_to_exp_base(bases: &[Self]) -> Vec<Self::ExpBase>;
}

pub trait PrimeScalarMul<F: PrimeField>: ScalarMul<F> + ScalarMul<F::BigInt> {
    /// Returns a fixed generator of this group.
    #[must_use]
    fn generator() -> Self;
}

pub trait PrimeScalarExp<F: PrimeField>: ScalarExp<F> + ScalarExp<F::BigInt> {
    /// Returns a fixed generator of this group.
    #[must_use]
    fn generator() -> Self;
}
