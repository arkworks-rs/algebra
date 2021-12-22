#![no_std]

extern crate ark_ff;
pub use ark_ff::*;

#[cfg(any(feature = "bls12_381_scalar_field", feature = "bls12_381_curve"))]
pub mod bls12_381;

#[cfg(feature = "mnt6_753")]
pub mod mnt6_753;

#[cfg(any(
    feature = "mnt4_753_scalar_field",
    feature = "mnt4_753_base_field",
    feature = "mnt4_753_curve"
))]
pub mod mnt4_753;

#[cfg(any(
    feature = "bn384_small_two_adicity_scalar_field",
    feature = "bn384_small_two_adicity_base_field",
    feature = "bn384_small_two_adicity_curve"
))]
pub mod bn384_small_two_adicity;
