//! This module implements the R1CS equivalent of `ark_curve25519`.
//! It requires a curve that embeds curve25519.

mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
