// Implements AddAssign on Self by deferring to an implementation on &Self
#[macro_export]
macro_rules! impl_additive_ops_from_ref {
    ($type: ident, $params: ident) => {
        impl<P: $params> core::ops::Add<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn add(self, other: Self) -> Self {
                let mut result = self;
                result += &other;
                result
            }
        }

        impl<'a, P: $params> core::ops::Add<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn add(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result += &*other;
                result
            }
        }

        impl<'b, P: $params> core::ops::Add<$type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn add(self, mut other: $type<P>) -> $type<P> {
                other += self;
                other
            }
        }

        impl<'a, 'b, P: $params> core::ops::Add<&'a $type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn add(self, other: &'a $type<P>) -> $type<P> {
                let mut result = *self;
                result += &*other;
                result
            }
        }

        impl<'a, 'b, P: $params> core::ops::Add<&'a mut $type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn add(self, other: &'a mut $type<P>) -> $type<P> {
                let mut result = *self;
                result += &*other;
                result
            }
        }

        impl<'b, P: $params> core::ops::Sub<$type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn sub(self, other: $type<P>) -> $type<P> {
                let mut result = *self;
                result -= &other;
                result
            }
        }

        impl<'a, 'b, P: $params> core::ops::Sub<&'a $type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn sub(self, other: &'a $type<P>) -> $type<P> {
                let mut result = *self;
                result -= &*other;
                result
            }
        }

        impl<'a, 'b, P: $params> core::ops::Sub<&'a mut $type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn sub(self, other: &'a mut $type<P>) -> $type<P> {
                let mut result = *self;
                result -= &*other;
                result
            }
        }

        impl<P: $params> core::ops::Sub<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn sub(self, other: Self) -> Self {
                let mut result = self;
                result -= &other;
                result
            }
        }

        impl<'a, P: $params> core::ops::Sub<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn sub(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result -= &*other;
                result
            }
        }

        impl<P: $params> core::iter::Sum<Self> for $type<P> {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::zero(), core::ops::Add::add)
            }
        }

        impl<'a, P: $params> core::iter::Sum<&'a Self> for $type<P> {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::zero(), core::ops::Add::add)
            }
        }

        impl<P: $params> core::ops::AddAssign<Self> for $type<P> {
            fn add_assign(&mut self, other: Self) {
                *self += &other
            }
        }

        impl<P: $params> core::ops::SubAssign<Self> for $type<P> {
            fn sub_assign(&mut self, other: Self) {
                *self -= &other
            }
        }

        impl<'a, P: $params> core::ops::AddAssign<&'a mut Self> for $type<P> {
            fn add_assign(&mut self, other: &'a mut Self) {
                *self += &*other
            }
        }

        impl<'a, P: $params> core::ops::SubAssign<&'a mut Self> for $type<P> {
            fn sub_assign(&mut self, other: &'a mut Self) {
                *self -= &*other
            }
        }
    };
}

// Implements `MulAssign` and `DivAssign` by deferring to an implementation on &Self
#[macro_export]
macro_rules! impl_multiplicative_ops_from_ref {
    ($type: ident, $params: ident) => {
        impl<P: $params> core::ops::Mul<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn mul(self, other: Self) -> Self {
                let mut result = self;
                result *= &other;
                result
            }
        }

        impl<P: $params> core::ops::Div<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn div(self, other: Self) -> Self {
                let mut result = self;
                result.div_assign(&other);
                result
            }
        }

        impl<'a, P: $params> core::ops::Mul<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn mul(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result *= &*other;
                result
            }
        }

        impl<'a, P: $params> core::ops::Div<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn div(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result.div_assign(&*other);
                result
            }
        }

        impl<'b, P: $params> core::ops::Mul<$type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn mul(self, mut other: $type<P>) -> $type<P> {
                other *= self;
                other
            }
        }

        impl<'a, 'b, P: $params> core::ops::Mul<&'a $type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn mul(self, other: &'a $type<P>) -> $type<P> {
                let mut result = *self;
                result *= &*other;
                result
            }
        }

        impl<'a, 'b, P: $params> core::ops::Mul<&'a mut $type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn mul(self, other: &'a mut $type<P>) -> $type<P> {
                let mut result = *self;
                result *= &*other;
                result
            }
        }

        impl<'b, P: $params> core::ops::Div<$type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn div(self, other: $type<P>) -> $type<P> {
                let mut result = *self;
                result.div_assign(&other);
                result
            }
        }

        impl<'a, 'b, P: $params> core::ops::Div<&'a $type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn div(self, other: &'a $type<P>) -> $type<P> {
                let mut result = *self;
                result.div_assign(&*other);
                result
            }
        }

        impl<'a, 'b, P: $params> core::ops::Div<&'a mut $type<P>> for &'b $type<P> {
            type Output = $type<P>;

            #[inline]
            fn div(self, other: &'a mut $type<P>) -> $type<P> {
                let mut result = *self;
                result.div_assign(&*other);
                result
            }
        }

        impl<P: $params> core::iter::Product<Self> for $type<P> {
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::one(), core::ops::Mul::mul)
            }
        }

        impl<'a, P: $params> core::iter::Product<&'a Self> for $type<P> {
            fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::one(), Mul::mul)
            }
        }

        impl<P: $params> core::ops::MulAssign<Self> for $type<P> {
            fn mul_assign(&mut self, other: Self) {
                *self *= &other
            }
        }

        impl<'a, P: $params> core::ops::DivAssign<&'a mut Self> for $type<P> {
            fn div_assign(&mut self, other: &'a mut Self) {
                self.div_assign(&*other)
            }
        }

        impl<'a, P: $params> core::ops::MulAssign<&'a mut Self> for $type<P> {
            fn mul_assign(&mut self, other: &'a mut Self) {
                *self *= &*other
            }
        }

        impl<P: $params> core::ops::DivAssign<Self> for $type<P> {
            fn div_assign(&mut self, other: Self) {
                self.div_assign(&other)
            }
        }
    };
}
