#[cfg(feature = "mnt4_298_fr")]
pub mod fr;
#[cfg(feature = "mnt4_298_fr")]
pub use self::fr::*;

#[cfg(feature = "mnt4_298_fq")]
pub mod fq;
#[cfg(feature = "mnt4_298_fq")]
pub use self::fq::*;

#[cfg(feature = "mnt4_298")]
pub mod fq2;
#[cfg(feature = "mnt4_298")]
pub use self::fq2::*;

#[cfg(feature = "mnt4_298")]
pub mod fq4;
#[cfg(feature = "mnt4_298")]
pub use self::fq4::*;

#[cfg(all(feature = "mnt4_298", test))]
mod tests;
