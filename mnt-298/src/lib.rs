#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

#[cfg(any(feature = "mnt4_298", feature = "mnt4_298_fr", feature = "mnt4_298_fq"))]
pub mod mnt4_298;

#[cfg(feature = "mnt6_298")]
pub mod mnt6_298;

#[cfg(feature = "ed_on_mnt4_298")]
pub mod ed_on_mnt4_298;
