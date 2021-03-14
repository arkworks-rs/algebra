#[cfg(feature = "bn384_small_two_adicity_base_field")]
pub mod fq;
#[cfg(feature = "bn384_small_two_adicity_base_field")]
pub use fq::*;

#[cfg(feature = "bn384_small_two_adicity_scalar_field")]
pub mod fr;
#[cfg(feature = "bn384_small_two_adicity_scalar_field")]
pub use fr::*;

#[cfg(feature = "bn384_small_two_adicity_curve")]
pub mod g1;
#[cfg(feature = "bn384_small_two_adicity_curve")]
pub use g1::*;

#[cfg(test)]
mod tests;
