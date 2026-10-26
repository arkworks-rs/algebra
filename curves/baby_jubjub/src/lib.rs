#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

//! This library implements the Baby Jubjub Twisted Edwards curve compatible with ERC-2494
//!
//! Curve information:
//! * Base field: q =
//!   21888242871839275222246405745257275088548364400416034343698204186575808495617
//! * Scalar field: r =
//!   2736030358979909402780800718157159386076813972158567259200215660948447373041
//! * Curve equation: Ax^2 + y^2 = 1 + Dx^2y^2, where
//!    * A = 168700
//!    * D = 168696

#[cfg(feature = "r1cs")]
pub mod constraints;
mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
