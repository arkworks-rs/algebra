#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

//! This library implements the ed25519 twisted Edwards curve.
//!
//! Curve information:
//! * Base field: q =
//!   57896044618658097711785492504343953926634992332820282019728792003956564819949
//! * Scalar field: r =
//!   7237005577332262213973186563042994240857116359379907606001950938285454250989
//! * Curve equation: ax^2 + y^2 =1 + dx^2y^2, where
//!    * a = -1
//!    * d = -121665 / 121666

#[cfg(feature = "r1cs")]
pub mod constraints;
mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
