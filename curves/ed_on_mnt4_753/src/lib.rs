#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

//! This library implements a twisted Edwards curve whose base field is the
//! scalar field of the curve MNT4-753. This allows defining cryptographic
//! primitives that use elliptic curves over the scalar field of the latter
//! curve.
//!
//! Curve information:
//! * Base field: q = 41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888458477323173057491593855069696241854796396165721416325350064441470418137846398469611935719059908164220784476160001
//! * Scalar field: r = 5237311370989869175293026848905079641021338739994243633972937865128169101571388346632361720473792365177258871486054600656048925740061347509722287043067341250552640264308621296888446513816907173362124418513727200975392177480577
//! * Valuation(q - 1, 2) = 30
//! * Valuation(r - 1, 2) = 7
//! * Curve equation: ax^2 + y^2 =1 + dx^2y^2, where
//!    * a = -1
//!    * d = 317690 mod q

#[cfg(feature = "r1cs")]
pub mod constraints;
mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
