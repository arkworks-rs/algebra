#![no_std]

#[cfg(any(feature = "bls12_381_scalar_field", feature = "bls12_381_curve"))]
pub mod bls12_381;

#[cfg(any(
    feature = "mnt4_753_scalar_field",
    feature = "mnt4_753_base_field",
    feature = "mnt4_753_curve"
))]
pub mod mnt4_753;
