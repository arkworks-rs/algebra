#![cfg_attr(not(feature = "std"), no_std)]
#![warn(
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    rust_2021_compatibility,
    clippy::missing_const_for_fn
)]
#![allow(clippy::op_ref, clippy::suspicious_op_assign_impl)]
#![deny(unsafe_code)]
#![doc = include_str!("../README.md")]

// Let proc-macros (MontConfig, SmallFpConfig, define_field, MontFp) that expand
// to `ark_ff::...` resolve when those expansions occur inside ark_ff itself,
// e.g. in the `test_helpers` module.
#[cfg(feature = "test_helpers")]
extern crate self as ark_ff;

#[macro_use]
pub mod biginteger;
pub use biginteger::{
    signed_mod_reduction, BigInt, BigInteger, BigInteger128, BigInteger256, BigInteger320,
    BigInteger384, BigInteger448, BigInteger64, BigInteger768, BigInteger832,
};

#[macro_use]
pub mod fields;
pub use self::fields::*;

pub(crate) mod bits;
pub use bits::*;

pub(crate) mod const_helpers;

pub use ark_std::UniformRand;

mod to_field_vec;
pub use to_field_vec::ToConstraintField;

#[doc(hidden)]
pub use ark_ff_asm::*;
#[doc(hidden)]
pub use ark_std::vec;

#[cfg(feature = "test_helpers")]
#[doc(hidden)]
pub mod test_helpers;

pub mod prelude {
    pub use crate::{
        biginteger::BigInteger,
        fields::{Field, PrimeField},
        One, Zero,
    };
    pub use ark_std::UniformRand;
}
