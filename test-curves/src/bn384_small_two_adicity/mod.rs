#[cfg(feature = "bn384_small_two_adicity_base_field")]
pub use ark_ff::test_helpers::bn384_small_two_adicity::fq::*;

#[cfg(feature = "bn384_small_two_adicity_scalar_field")]
pub use ark_ff::test_helpers::bn384_small_two_adicity::fr::*;

#[cfg(feature = "bn384_small_two_adicity_curve")]
pub mod g1;
#[cfg(feature = "bn384_small_two_adicity_curve")]
pub use g1::*;

#[cfg(test)]
mod tests;
