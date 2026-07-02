#[cfg(feature = "base_field")]
pub mod fq;
#[cfg(feature = "base_field")]
pub use self::fq::*;
#[cfg(feature = "base_field")]
mod fq_sqrt_table;

#[cfg(feature = "scalar_field")]
pub mod fr;
#[cfg(feature = "scalar_field")]
pub use self::fr::*;
#[cfg(feature = "scalar_field")]
mod fr_sqrt_table;

#[cfg(all(feature = "curve", test))]
mod tests;
