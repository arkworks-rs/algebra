#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

//! This library implements the secp256r1 curve.
//! Source: <https://neuromancer.sk/std/secg/secp256r1>
//!
//! Curve information:
//! * Base field: q =
//!   0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
//! * Scalar field: r =
//!   0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
//! * a = -3
//! * b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
//! * Curve equation: y^2 = x^3 + ax + b

#[cfg(feature = "r1cs")]
pub mod constraints;
mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
