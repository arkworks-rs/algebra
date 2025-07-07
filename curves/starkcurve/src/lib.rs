#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

//! This library implements [the Stark curve](https://docs.starknet.io/architecture/cryptography/#the_stark_curve)
//! An elliptic curve defined over the STARK field by equation y² ≡ x³ + α·x + β (mod q)
//!
//! Where:
//! * α = 1
//! * β = 3141592653589793238462643383279502884197169399375105820974944592307816406665
//! * q = 3618502788666131213697322783095070105623107215331596699973092056135872020481
//! * or, q = 2^251 + 17 * 2^192 + 1
//!
//! Generator point:
//! * x = 0x1ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca
//! * y = 0x5668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f
//!
//! Curve information:
//! StarkCurve:
//! * Base field: q =
//!   3618502788666131213697322783095070105623107215331596699973092056135872020481
//! * Scalar field: r =
//!   3618502788666131213697322783095070105526743751716087489154079457884512865583
//! * Curve equation: y^2 = x^3 + x + β (mod q)

#[cfg(feature = "r1cs")]
pub mod constraints;
mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
