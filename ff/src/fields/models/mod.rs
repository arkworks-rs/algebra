use ark_std::{
    cmp::{Ord, Ordering, PartialOrd},
    fmt::{Display, Formatter, Result as FmtResult},
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    str::FromStr,
};
use num_traits::{One, Zero};

use crate::{
    biginteger::{
        arithmetic as fa, BigInteger as _BigInteger, BigInteger256, BigInteger320, BigInteger384,
        BigInteger64, BigInteger768, BigInteger832,
    },
    bytes::{FromBytes, ToBytes},
    fields::{FftField, Field, FpParameters, LegendreSymbol, PrimeField, SquareRootField},
};
use ark_serialize::*;
// Represents a prime field element that might have small magnitude.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SmallFp<F: PrimeField> {
    Small(i8),
    Full(F),
}

impl<F: PrimeField> From<i8> for SmallFp<F> {
    fn from(other: i8) -> Self {
        Self::Small(other)
    }
}

impl<F: PrimeField> From<F> for SmallFp<F> {
    fn from(other: F) -> Self {
        Self::Full(other)
    }
}

impl<F: PrimeField + From<Self>> Zero for SmallFp<F> {
    fn zero() -> Self {
        Self::Small(0)
    }

    fn is_zero(&self) -> bool {
        match self {
            Self::Small(f) => f.is_zero(),
            Self::Full(f) => f.is_zero(),
        }
    }
}

impl<F: PrimeField> Neg for SmallFp<F> {
    type Output = Self;
    fn neg(self) -> Self {
        match self {
            Self::Small(f) => f.checked_neg().map(Self::from).expect("cannot negate"),
            Self::Full(f) => Self::from(-f),
        }
    }
}

impl<F: PrimeField + From<Self>> Add<Self> for SmallFp<F> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        use SmallFp::*;
        match (self, other) {
            (Small(f1), Small(f2)) => f1.checked_add(f2).expect("cannot multiply these small numbers").into(),
            (Full(f1), Full(f2)) => Self::from(f1 + f2),
            (_, Full(f2)) => Self::from(F::from(self) + f2),
            (Full(f2), _) => Self::from(F::from(other) + f2),
        }
    }
}

impl<F: PrimeField> Mul<F> for SmallFp<F> 
where
    F: From<Self>
{
    type Output = F;
    fn mul(self, mut other: F) -> Self::Output {
        match self {
            Self::Full(f) => f * other,
            Self::Small(f) => {
                let is_negative = f.is_negative();
                // TODO: replace with `unsigned_abs` once it is stable (1.51).
                let f = f.wrapping_abs() as u8;
                match f {
                    0 => other = F::zero(),
                    1 => {},
                    2 => { 
                        other.double_in_place();
                    },
                    3 => { 
                        other += other.double();
                    },
                    4 => { 
                        other.double_in_place().double_in_place();
                    },
                    5 => { 
                        let other_copy = other;
                        other.double_in_place().double_in_place();
                        other += other_copy;
                    },
                    6 => { 
                        other += other.double(); // self *= 3
                        other.double_in_place(); // self *= 2
                    },
                    7 => { 
                        let mut result = other;
                        result.double_in_place().double_in_place().double_in_place();
                        result -= other;
                        other = result;
                    },
                    _ => {
                        other *= F::from(f);
                    },
                };
                if is_negative {
                    -other 
                } else {
                    other
                }
            }
        }
    }
}

impl<F: PrimeField> PartialEq<i8> for SmallFp<F> 
where
    F: From<Self>
{
    fn eq(&self, other: &i8) -> bool {
        *self == Self::from(*other)
    }
}

impl_Fp!(Fp64, Fp64Parameters, BigInteger64, BigInteger64, 1);
impl_Fp!(Fp256, Fp256Parameters, BigInteger256, BigInteger256, 4);
impl_Fp!(Fp320, Fp320Parameters, BigInteger320, BigInteger320, 5);
impl_Fp!(Fp384, Fp384Parameters, BigInteger384, BigInteger384, 6);
impl_Fp!(Fp768, Fp768Parameters, BigInteger768, BigInteger768, 12);
impl_Fp!(Fp832, Fp832Parameters, BigInteger832, BigInteger832, 13);

pub mod fp2;
pub use self::fp2::*;

pub mod fp3;
pub use self::fp3::*;

pub mod fp4;
pub use self::fp4::*;

pub mod fp6_2over3;

pub mod fp6_3over2;
pub use self::fp6_3over2::*;

pub mod fp12_2over3over2;
pub use self::fp12_2over3over2::*;

pub mod quadratic_extension;
pub use quadratic_extension::*;

pub mod cubic_extension;
pub use cubic_extension::*;
