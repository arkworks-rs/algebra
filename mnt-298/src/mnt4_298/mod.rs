//! This module implements the MNT4_298 curve generated by
//! [[BCTV14]](https://eprint.iacr.org/2014/595).  The name denotes that it is a
//! Miyaji--Nakabayashi--Takano curve of embedding degree 4, defined over a 298-bit (prime) field.
//! The main feature of this curve is that its scalar field and base field respectively equal the
//! base field and scalar field of MNT6_298.
//!
//!
//! Curve information:
//! * Base field: q = 475922286169261325753349249653048451545124879242694725395555128576210262817955800483758081
//! * Scalar field: r = 475922286169261325753349249653048451545124878552823515553267735739164647307408490559963137
//! * valuation(q - 1, 2) = 17
//! * valuation(r - 1, 2) = 34
//! * G1 curve equation: y^2 = x^3 + ax + b, where
//!    * a = 2
//!    * b = 423894536526684178289416011533888240029318103673896002803341544124054745019340795360841685
//! * G2 curve equation: y^2 = x^3 + Ax + B, where
//!    * A = Fq2 = (a * NON_RESIDUE, 0)
//!    * B = Fq2(0, b * NON_RESIDUE)
//!    * NON_RESIDUE = 17 is the quadratic non-residue used for constructing the extension field Fq2

#[cfg(feature = "mnt4_298")]
mod curves;
#[cfg(any(feature = "mnt4_298_fr", feature = "mnt4_298_fq"))]
mod fields;

#[cfg(feature = "mnt4_298")]
pub use curves::*;
#[cfg(any(feature = "mnt4_298_fr", feature = "mnt4_298_fq"))]
pub use fields::*;
