#![cfg_attr(not(feature = "std"), no_std)]
#![deny(warnings, unused, future_incompatible, nonstandard_style, rust_2018_idioms)]

#[cfg(any(feature = "bn254", feature = "bn254_fr"))]
pub mod bn254;

#[cfg(feature = "ed_on_bn254")]
pub mod ed_on_bn254;
