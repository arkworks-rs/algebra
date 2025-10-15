use crate::fields::models::small_fp::small_fp_backend::{SmallFp, SmallFpConfig};
use crate::{BigInt, PrimeField};

impl<P: SmallFpConfig> From<u128> for SmallFp<P> {
    fn from(other: u128) -> Self {
        let bigint = BigInt::<2>::new([other as u64, (other >> 64) as u64]);
        Self::from_bigint(bigint).unwrap()
    }
}

impl<P: SmallFpConfig> From<i128> for SmallFp<P> {
    fn from(other: i128) -> Self {
        let abs = other.unsigned_abs().into();
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: SmallFpConfig> From<bool> for SmallFp<P> {
    fn from(other: bool) -> Self {
        if other == true {
            P::ONE
        } else {
            P::ZERO
        }
    }
}

impl<P: SmallFpConfig> From<u64> for SmallFp<P> {
    fn from(other: u64) -> Self {
        Self::from(other as u128)
    }
}

impl<P: SmallFpConfig> From<i64> for SmallFp<P> {
    fn from(other: i64) -> Self {
        let abs = other.unsigned_abs().into();
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: SmallFpConfig> From<u32> for SmallFp<P> {
    fn from(other: u32) -> Self {
        Self::from(other as u128)
    }
}

impl<P: SmallFpConfig> From<i32> for SmallFp<P> {
    fn from(other: i32) -> Self {
        let abs = other.unsigned_abs().into();
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: SmallFpConfig> From<u16> for SmallFp<P> {
    fn from(other: u16) -> Self {
        let other_as_t = match P::T::try_from(other.into()) {
            Ok(val) => val,
            Err(_) => {
                let modulus_as_u128: u128 = P::MODULUS.into();
                let reduced = (other as u128) % modulus_as_u128;
                P::T::try_from(reduced).unwrap_or_else(|_| panic!("Reduced value should fit in T"))
            },
        };
        let val = other_as_t % P::MODULUS;
        SmallFp::new(val)
    }
}

impl<P: SmallFpConfig> From<i16> for SmallFp<P> {
    fn from(other: i16) -> Self {
        let abs = other.unsigned_abs().into();
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: SmallFpConfig> From<u8> for SmallFp<P> {
    fn from(other: u8) -> Self {
        let other_as_t = match P::T::try_from(other.into()) {
            Ok(val) => val,
            Err(_) => {
                let modulus_as_u128: u128 = P::MODULUS.into();
                let reduced = (other as u128) % modulus_as_u128;
                P::T::try_from(reduced).unwrap_or_else(|_| panic!("Reduced value should fit in T"))
            },
        };
        let val = other_as_t % P::MODULUS;
        SmallFp::new(val)
    }
}

impl<P: SmallFpConfig> From<i8> for SmallFp<P> {
    fn from(other: i8) -> Self {
        let abs = other.unsigned_abs().into();
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: SmallFpConfig> From<num_bigint::BigUint> for SmallFp<P> {
    #[inline]
    fn from(val: num_bigint::BigUint) -> SmallFp<P> {
        SmallFp::from_le_bytes_mod_order(&val.to_bytes_le())
    }
}

impl<P: SmallFpConfig> From<SmallFp<P>> for num_bigint::BigUint {
    #[inline(always)]
    fn from(other: SmallFp<P>) -> Self {
        other.into_bigint().into()
    }
}

impl<P: SmallFpConfig> From<SmallFp<P>> for BigInt<2> {
    fn from(fp: SmallFp<P>) -> Self {
        fp.into_bigint()
    }
}

impl<P: SmallFpConfig> From<BigInt<2>> for SmallFp<P> {
    fn from(int: BigInt<2>) -> Self {
        Self::from_bigint(int).unwrap()
    }
}
