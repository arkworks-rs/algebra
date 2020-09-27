#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

#[cfg(any(feature = "mnt4_753", feature = "mnt4_753_fr", feature = "mnt4_753_fq"))]
pub mod mnt4_753;

#[cfg(feature = "mnt6_753")]
pub mod mnt6_753;

#[cfg(feature = "ed_on_mnt4_753")]
pub mod ed_on_mnt4_753;
