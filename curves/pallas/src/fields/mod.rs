#[cfg(feature = "base_field")]
pub mod fq;
#[cfg(feature = "base_field")]
pub use self::fq::*;

#[cfg(feature = "scalar_field")]
pub mod fr;
#[cfg(feature = "scalar_field")]
pub use self::fr::*;

#[cfg(all(feature = "curve", test))]
mod tests;
