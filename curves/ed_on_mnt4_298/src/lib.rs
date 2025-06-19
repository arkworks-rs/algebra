#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

//! This library implements a twisted Edwards curve whose base field is the
//! scalar field of the curve MNT4-298. This allows defining cryptographic
//! primitives that use elliptic curves over the scalar field of the latter
//! curve.
//!
//! Curve information:
//! * Base field: q =
//!   475922286169261325753349249653048451545124878552823515553267735739164647307408490559963137
//! * Scalar field: r =
//!   118980571542315331438337312413262112886281219744507561120271964887686106682370032123932631
//! * Valuation(q - 1, 2) = 30
//! * Valuation(r - 1, 2) = 1
//! * Curve equation: ax^2 + y^2 =1 + dx^2y^2, where
//!    * a = -1
//!    * d = 4212 mod q

#[cfg(feature = "r1cs")]
pub mod constraints;
mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
