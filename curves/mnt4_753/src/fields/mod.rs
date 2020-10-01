#[cfg(feature = "scalar_field")]
pub mod fr;
#[cfg(feature = "scalar_field")]
pub use self::fr::*;

#[cfg(feature = "base_field")]
pub mod fq;
#[cfg(feature = "base_field")]
pub use self::fq::*;

#[cfg(feature = "curve")]
pub mod fq2;
#[cfg(feature = "curve")]
pub use self::fq2::*;

#[cfg(feature = "curve")]
pub mod fq4;
#[cfg(feature = "curve")]
pub use self::fq4::*;

#[cfg(all(feature = "curve", test))]
mod tests;
