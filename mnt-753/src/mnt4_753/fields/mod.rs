#[cfg(feature = "mnt4_753_fr")]
pub mod fr;
#[cfg(feature = "mnt4_753_fr")]
pub use self::fr::*;

#[cfg(feature = "mnt4_753_fq")]
pub mod fq;
#[cfg(feature = "mnt4_753_fq")]
pub use self::fq::*;

#[cfg(feature = "mnt4_753")]
pub mod fq2;
#[cfg(feature = "mnt4_753")]
pub use self::fq2::*;

#[cfg(feature = "mnt4_753")]
pub mod fq4;
#[cfg(feature = "mnt4_753")]
pub use self::fq4::*;

#[cfg(all(feature = "mnt4_753", test))]
mod tests;
