#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

//! This library implements the MNT6_298 curve generated in
//! [\[BCTV14\]](https://eprint.iacr.org/2014/595).  The name denotes that it is a
//! Miyaji--Nakabayashi--Takano curve of embedding degree 6, defined over a
//! 298-bit (prime) field. The main feature of this curve is that its scalar
//! field and base field respectively equal the base field and scalar field of
//! MNT4_298.
//!
//!
//! Curve information:
//! * Base field: q =
//!   475922286169261325753349249653048451545124878552823515553267735739164647307408490559963137
//! * Scalar field: r =
//!   475922286169261325753349249653048451545124879242694725395555128576210262817955800483758081
//! * valuation(q - 1, 2) = 34
//! * valuation(r - 1, 2) = 17
//! * G1 curve equation: y^2 = x^3 + ax + b, where
//!    * a = 11
//!    * b = 106700080510851735677967319632585352256454251201367587890185989362936000262606668469523074
//! * G2 curve equation: y^2 = x^3 + Ax + B, where
//!    * A = Fq2 = (0, 0, a)
//!    * B = Fq2(b * NON_RESIDUE, 0, 0)
//!    * NON_RESIDUE = 5 is the cubic non-residue used to construct the field
//!      extension Fq3

#[cfg(feature = "r1cs")]
pub mod constraints;
mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
