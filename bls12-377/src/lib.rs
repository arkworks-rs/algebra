#![cfg_attr(not(feature = "std"), no_std)]
#![deny(warnings, unused, future_incompatible, nonstandard_style, rust_2018_idioms)]

#[cfg(any(feature = "bls12_377", feature = "bls12_377_fr", feature = "bls12_377_fq"))]
pub mod bls12_377;

#[cfg(feature = "ed_on_bls12_377")]
pub mod ed_on_bls12_377;

#[cfg(feature = "bw6_761")]
pub mod bw6_761;

#[cfg(feature = "ed_on_bw6_761")]
pub mod ed_on_bw6_761;

#[cfg(feature = "cp6_782")]
pub mod cp6_782;

#[cfg(feature = "ed_on_cp6_782")]
pub mod ed_on_cp6_782;