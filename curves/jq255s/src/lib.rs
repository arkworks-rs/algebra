#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

//!
//! This a test curve to confirm the correctness of the double-odd curve implementation, proposed
//! by Thomas Pornin (<https://doubleodd.group/>). We implement tests that are equivalent to the
//! tests of implementations of this curve by Pornin.
//!
//! Curve information:
//! * Base field:
//!   q = 2^{255} - 3957
//!   = 57896044618658097711785492504343953926634992332820282019728792003956564816011
//! * Scalar field:
//!   2r = 2(2^{254}+56904135270672826811114353017034461895)
//!   = 57896044618658097711785492504343953926748800603361627673351020709990633743758
//!   r = 28948022309329048855892746252171976963374400301680813836675510354995316871879
//! * a = -1
//! * b = 1/2
//! * Curve equation:
//!   y^2 = x(x^2 + ax + b)
//!   = x(x^2 - x + 1/2)

#[cfg(feature = "r1cs")]
pub mod constraints;
mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
