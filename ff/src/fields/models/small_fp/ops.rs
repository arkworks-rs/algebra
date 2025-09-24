use crate::fields::models::small_fp::small_fp_backend::{SmallFp, SmallFpConfig};
use crate::{Field, One, Zero};
use ark_std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

impl<P: SmallFpConfig> Neg for SmallFp<P> {
    type Output = Self;
    #[inline]
    fn neg(mut self) -> Self {
        P::neg_in_place(&mut self);
        self
    }
}

impl<P: SmallFpConfig> Add<&SmallFp<P>> for SmallFp<P> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &Self) -> Self {
        self += other;
        self
    }
}

impl<P: SmallFpConfig> Sub<&SmallFp<P>> for SmallFp<P> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &Self) -> Self {
        self -= other;
        self
    }
}

impl<P: SmallFpConfig> Mul<&SmallFp<P>> for SmallFp<P> {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: &Self) -> Self {
        self *= other;
        self
    }
}

impl<P: SmallFpConfig> Div<&SmallFp<P>> for SmallFp<P> {
    type Output = Self;

    /// Returns `self * other.inverse()` if `other.inverse()` is `Some`, and
    /// panics otherwise.
    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(mut self, other: &Self) -> Self {
        match other.inverse() {
            Some(inv) => {
                self *= &inv;
                self
            },
            None => panic!("Division by zero in finite field"),
        }
    }
}

impl<'b, P: SmallFpConfig> Add<&'b SmallFp<P>> for &SmallFp<P> {
    type Output = SmallFp<P>;

    #[inline]
    fn add(self, other: &'b SmallFp<P>) -> SmallFp<P> {
        let mut result = *self;
        result += other;
        result
    }
}

impl<P: SmallFpConfig> Sub<&SmallFp<P>> for &SmallFp<P> {
    type Output = SmallFp<P>;

    #[inline]
    fn sub(self, other: &SmallFp<P>) -> SmallFp<P> {
        let mut result = *self;
        result -= other;
        result
    }
}

impl<P: SmallFpConfig> Mul<&SmallFp<P>> for &SmallFp<P> {
    type Output = SmallFp<P>;

    #[inline]
    fn mul(self, other: &SmallFp<P>) -> SmallFp<P> {
        let mut result = *self;
        result *= other;
        result
    }
}

impl<P: SmallFpConfig> Div<&SmallFp<P>> for &SmallFp<P> {
    type Output = SmallFp<P>;

    #[inline]
    fn div(self, other: &SmallFp<P>) -> SmallFp<P> {
        let mut result = *self;
        result.div_assign(other);
        result
    }
}

impl<P: SmallFpConfig> AddAssign<&Self> for SmallFp<P> {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        P::add_assign(self, other)
    }
}

impl<P: SmallFpConfig> SubAssign<&Self> for SmallFp<P> {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        P::sub_assign(self, other);
    }
}

impl<P: SmallFpConfig> core::ops::Add<Self> for SmallFp<P> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: Self) -> Self {
        self += &other;
        self
    }
}

impl<'a, P: SmallFpConfig> core::ops::Add<&'a mut Self> for SmallFp<P> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a mut Self) -> Self {
        self += &*other;
        self
    }
}

impl<P: SmallFpConfig> core::ops::Sub<Self> for SmallFp<P> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: Self) -> Self {
        self -= &other;
        self
    }
}

impl<'a, P: SmallFpConfig> core::ops::Sub<&'a mut Self> for SmallFp<P> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &'a mut Self) -> Self {
        self -= &*other;
        self
    }
}

impl<P: SmallFpConfig> core::iter::Sum<Self> for SmallFp<P> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

impl<'a, P: SmallFpConfig> core::iter::Sum<&'a Self> for SmallFp<P> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

impl<P: SmallFpConfig> core::ops::AddAssign<Self> for SmallFp<P> {
    #[inline(always)]
    fn add_assign(&mut self, other: Self) {
        *self += &other
    }
}

impl<P: SmallFpConfig> core::ops::SubAssign<Self> for SmallFp<P> {
    #[inline(always)]
    fn sub_assign(&mut self, other: Self) {
        *self -= &other
    }
}

impl<'a, P: SmallFpConfig> core::ops::AddAssign<&'a mut Self> for SmallFp<P> {
    #[inline(always)]
    fn add_assign(&mut self, other: &'a mut Self) {
        *self += &*other
    }
}

impl<'a, P: SmallFpConfig> core::ops::SubAssign<&'a mut Self> for SmallFp<P> {
    #[inline(always)]
    fn sub_assign(&mut self, other: &'a mut Self) {
        *self -= &*other
    }
}

impl<P: SmallFpConfig> MulAssign<&Self> for SmallFp<P> {
    fn mul_assign(&mut self, other: &Self) {
        P::mul_assign(self, other)
    }
}

/// Computes `self *= other.inverse()` if `other.inverse()` is `Some`, and
/// panics otherwise.
impl<P: SmallFpConfig> DivAssign<&Self> for SmallFp<P> {
    #[inline(always)]
    fn div_assign(&mut self, other: &Self) {
        match other.inverse() {
            Some(inv) => {
                *self *= &inv;
            },
            None => panic!("Division by zero in finite field"),
        }
    }
}

impl<P: SmallFpConfig> core::ops::Mul<Self> for SmallFp<P> {
    type Output = Self;

    #[inline(always)]
    fn mul(mut self, other: Self) -> Self {
        self *= &other;
        self
    }
}

impl<P: SmallFpConfig> core::ops::Div<Self> for SmallFp<P> {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: Self) -> Self {
        self.div_assign(&other);
        self
    }
}

impl<'a, P: SmallFpConfig> core::ops::Mul<&'a mut Self> for SmallFp<P> {
    type Output = Self;

    #[inline(always)]
    fn mul(mut self, other: &'a mut Self) -> Self {
        self *= &*other;
        self
    }
}

impl<'a, P: SmallFpConfig> core::ops::Div<&'a mut Self> for SmallFp<P> {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: &'a mut Self) -> Self {
        self.div_assign(&*other);
        self
    }
}

impl<P: SmallFpConfig> core::iter::Product<Self> for SmallFp<P> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), core::ops::Mul::mul)
    }
}

impl<'a, P: SmallFpConfig> core::iter::Product<&'a Self> for SmallFp<P> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::one(), Mul::mul)
    }
}

impl<P: SmallFpConfig> core::ops::MulAssign<Self> for SmallFp<P> {
    #[inline(always)]
    fn mul_assign(&mut self, other: Self) {
        *self *= &other
    }
}

impl<'a, P: SmallFpConfig> core::ops::DivAssign<&'a mut Self> for SmallFp<P> {
    #[inline(always)]
    fn div_assign(&mut self, other: &'a mut Self) {
        self.div_assign(&*other)
    }
}

impl<'a, P: SmallFpConfig> core::ops::MulAssign<&'a mut Self> for SmallFp<P> {
    #[inline(always)]
    fn mul_assign(&mut self, other: &'a mut Self) {
        *self *= &*other
    }
}

impl<P: SmallFpConfig> core::ops::DivAssign<Self> for SmallFp<P> {
    #[inline(always)]
    fn div_assign(&mut self, other: Self) {
        self.div_assign(&other)
    }
}

impl<P: SmallFpConfig> zeroize::Zeroize for SmallFp<P> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.value = P::ZERO.value;
    }
}
