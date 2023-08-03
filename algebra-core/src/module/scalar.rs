use ark_std::fmt::Debug;

use crate::biginteger::{signed_mod_reduction, arithmetic::{sbb_for_sub_with_borrow, adc_for_add_with_carry}};

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub enum Sign {
    Negative = -1,
    #[default]
    Positive = 1,
}

impl Sign {
    pub fn is_negative(&self) -> bool {
        matches!(self, Sign::Negative)
    }

    pub fn is_positive(&self) -> bool {
        matches!(self, Sign::Positive)
    }
}

pub trait Scalar: Send + Sync + Copy + Debug {
    const MAX_BIT_SIZE: Option<u32>;
    type U8Ref: AsRef<[u8]>;
    type U64Ref: AsRef<[u64]>;

    fn as_bytes(&self) -> (Sign, Self::U8Ref);

    fn as_u64s(&self) -> (Sign, Self::U64Ref);

    /// Returns the windowed non-adjacent form of `self`, for a window of size `w`.
    fn find_wnaf(&self, w: usize) -> Option<Vec<i64>> {
        // w > 2 due to definition of wNAF, and w < 64 to make sure that `i64`
        // can fit each signed digit
        if (2..64).contains(&w) {
            let mut res = vec![];
            let mut e = self.as_u64s().1.as_ref().to_vec();

            while !is_zero(&e) {
                let z: i64;
                if is_odd(&e) {
                    z = signed_mod_reduction(e[0], 1 << w);
                    if z >= 0 {
                        sub_with_borrow(&mut e, z as u64);
                    } else {
                        add_with_carry(&mut e,  (-z) as u64);
                    }
                } else {
                    z = 0;
                }
                res.push(z);
                div2(&mut e);
            }

            Some(res)
        } else {
            None
        }
    }
}

fn is_zero(a: &[u64]) -> bool {
    a.iter().all(|x| *x == 0)
}

fn is_odd(a: &[u64]) -> bool {
    a[0] % 2 == 1
}

fn sub_with_borrow(a: &mut [u64], b: u64) {
    let mut borrow = sbb_for_sub_with_borrow(&mut a[0], b, 0);
    for a in &mut a[1..] {
        borrow = sbb_for_sub_with_borrow(a, 0, borrow);
    }
}

fn add_with_carry(a: &mut [u64], b: u64) {
    let mut carry = adc_for_add_with_carry(&mut a[0], b, 0);
    for a in &mut a[1..] {
        carry = adc_for_add_with_carry(a, 0, carry);
    }
}

fn div2(a: &mut [u64]) {
    let mut t = 0;
    for a in a.iter_mut().rev() {
        let t2 = *a << 63;
        *a >>= 1;
        *a |= t;
        t = t2;
    }
}

macro_rules! impl_scalar_unsigned {
    ($t:ty) => {
        impl Scalar for $t {
            const MAX_BIT_SIZE: Option<u32> = Some(core::mem::size_of::<$t>() as u32 * 8);
            type U8Ref = [u8; core::mem::size_of::<$t>()];
            type U64Ref = [u64; (core::mem::size_of::<$t>() + 7) / 8];

            fn as_bytes(&self) -> (Sign, Self::U8Ref) {
                (Sign::Positive, self.to_le_bytes())
            }

            fn as_u64s(&self) -> (Sign, Self::U64Ref) {
                let mut res = [0u64; (core::mem::size_of::<$t>() + 7) / 8];
                for (chunk, res) in self.to_le_bytes().chunks_mut(8).zip(&mut res) {
                    chunk.reverse();
                    *res = chunk.iter().fold(0u64, |acc, &x| (acc << 8) | x as u64);
                }
                (Sign::Positive, res)
            }
        }
    };
}

impl_scalar_unsigned!(u8);
impl_scalar_unsigned!(u16);
impl_scalar_unsigned!(u32);
impl_scalar_unsigned!(u64);
impl_scalar_unsigned!(u128);

macro_rules! impl_scalar_signed {
    ($t:ty) => {
        impl Scalar for $t {
            const MAX_BIT_SIZE: Option<u32> = Some(core::mem::size_of::<$t>() as u32 * 8);
            type U8Ref = [u8; core::mem::size_of::<$t>()];
            type U64Ref = [u64; (core::mem::size_of::<$t>() + 7) / 8];

            fn as_bytes(&self) -> (Sign, Self::U8Ref) {
                let sign = if *self < 0 {
                    Sign::Negative
                } else {
                    Sign::Positive
                };
                let val = self.unsigned_abs();
                (sign, val.to_le_bytes())
            }

            fn as_u64s(&self) -> (Sign, Self::U64Ref) {
                let sign = if *self < 0 {
                    Sign::Negative
                } else {
                    Sign::Positive
                };
                let mut res = [0u64; (core::mem::size_of::<$t>() + 7) / 8];
                let val = self.unsigned_abs();
                for (chunk, res) in val.to_le_bytes().chunks_mut(8).zip(&mut res) {
                    chunk.reverse();
                    *res = chunk.iter().fold(0u64, |acc, &x| (acc << 8) | x as u64);
                }
                (sign, res)
            }
        }
    };
}

impl_scalar_signed!(i8);
impl_scalar_signed!(i16);
impl_scalar_signed!(i32);
impl_scalar_signed!(i64);
impl_scalar_signed!(i128);

impl<'a> Scalar for &'a [u64] {
    const MAX_BIT_SIZE: Option<u32> = None;
    type U8Ref = Vec<u8>;
    type U64Ref = Self;

    fn as_bytes(&self) -> (Sign, Self::U8Ref) {
        (
            Sign::Positive,
            self.iter().map(|x| x.to_le_bytes()).flatten().collect(),
        )
    }

    fn as_u64s(&self) -> (Sign, Self::U64Ref) {
        (Sign::Positive, self)
    }
}

impl<'a, S: Scalar> Scalar for &'a S {
    const MAX_BIT_SIZE: Option<u32> = S::MAX_BIT_SIZE;
    type U8Ref = S::U8Ref;
    type U64Ref = S::U64Ref;

    fn as_bytes(&self) -> (Sign, Self::U8Ref) {
        (*self).as_bytes()
    }

    fn as_u64s(&self) -> (Sign, Self::U64Ref) {
        (*self).as_u64s()
    }
}

#[cfg(test)]
mod tests {

    fn test() {
        todo!()
    }
}
