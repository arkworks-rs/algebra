use ark_std::fmt::Debug;

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
