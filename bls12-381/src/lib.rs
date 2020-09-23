#![cfg_attr(not(feature = "std"), no_std)]
#![deny(warnings, unused, future_incompatible, nonstandard_style, rust_2018_idioms)]

#[cfg(any(feature = "bls12_381", feature = "bls12_381_fr"))]
pub mod bls12_381;

#[cfg(feature = "ed_on_bls12_381")]
pub mod ed_on_bls12_381;