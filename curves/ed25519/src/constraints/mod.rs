//! This module implements the R1CS equivalent of `ark_ed25519`.
//! It requires a curve that embeds ed25519.

mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
