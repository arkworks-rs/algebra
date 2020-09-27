#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![cfg_attr(use_asm, feature(llvm_asm))]
#![cfg_attr(not(use_asm), forbid(unsafe_code))]
#![cfg_attr(use_asm, deny(unsafe_code))]

#[macro_use]
extern crate ark_std;

#[macro_use]
extern crate derivative;

#[cfg_attr(test, macro_use)]
pub mod bytes;
pub use self::bytes::*;

#[macro_use]
pub mod fields;
pub use self::fields::*;

pub mod biginteger;
pub use self::biginteger::*;

mod rand;
pub use self::rand::*;

mod to_field_vec;
pub use to_field_vec::ToConstraintField;

pub use num_traits::{One, Zero};

pub use ark_std::vec;

pub mod prelude {
    pub use crate::biginteger::BigInteger;

    pub use crate::fields::{Field, FpParameters, PrimeField, SquareRootField};

    pub use crate::rand::UniformRand;

    pub use num_traits::{One, Zero};
}

#[cfg(not(feature = "std"))]
fn error(_msg: &'static str) -> ark_std::io::Error {
    ark_std::io::Error
}

#[cfg(feature = "std")]
fn error(msg: &'static str) -> ark_std::io::Error {
    ark_std::io::Error::new(ark_std::io::ErrorKind::Other, msg)
}

/// Returns the base-2 logarithm of `x`.
///
/// ```
/// use algebra_core::log2;
///
/// assert_eq!(log2(16), 4);
/// assert_eq!(log2(17), 5);
/// assert_eq!(log2(1), 0);
/// assert_eq!(log2(0), 0);
/// assert_eq!(log2(usize::MAX), (core::mem::size_of::<usize>() * 8) as u32);
/// assert_eq!(log2(1 << 15), 15);
/// assert_eq!(log2(2usize.pow(18)), 18);
/// ```
pub fn log2(x: usize) -> u32 {
    if x == 0 {
        0
    } else if x.is_power_of_two() {
        1usize.leading_zeros() - x.leading_zeros()
    } else {
        0usize.leading_zeros() - x.leading_zeros()
    }
}
