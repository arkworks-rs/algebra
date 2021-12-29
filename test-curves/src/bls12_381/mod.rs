pub mod fr;
pub use fr::*;

#[cfg(feature = "bls12_381_curve")]
pub mod fq;
#[cfg(feature = "bls12_381_curve")]
pub mod fq2;
#[cfg(feature = "bls12_381_curve")]
pub mod fq6;
#[cfg(feature = "bls12_381_curve")]
pub mod g1;

#[cfg(feature = "bls12_381_curve")]
pub use {fq::*, fq2::*, fq6::*, g1::*};
#[cfg(test)]
mod tests;
