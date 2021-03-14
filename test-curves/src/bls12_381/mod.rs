pub mod fr;
pub use fr::*;

#[cfg(feature = "bls12_381_curve")]
pub mod fq;
#[cfg(feature = "bls12_381_curve")]
pub mod g1;

#[cfg(feature = "bls12_381_curve")]
pub use fq::*;
#[cfg(feature = "bls12_381_curve")]
pub use g1::*;

#[cfg(test)]
mod tests;
