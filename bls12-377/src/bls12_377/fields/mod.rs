#[cfg(feature = "bls12_377_fr")]
pub mod fr;
#[cfg(feature = "bls12_377_fr")]
pub use self::fr::*;

#[cfg(feature = "bls12_377_fq")]
pub mod fq;
#[cfg(feature = "bls12_377_fq")]
pub use self::fq::*;

#[cfg(feature = "bls12_377")]
pub mod fq2;
#[cfg(feature = "bls12_377")]
pub use self::fq2::*;

#[cfg(feature = "bls12_377")]
pub mod fq6;
#[cfg(feature = "bls12_377")]
pub use self::fq6::*;

#[cfg(feature = "bls12_377")]
pub mod fq12;
#[cfg(feature = "bls12_377")]
pub use self::fq12::*;

#[cfg(all(feature = "bls12_377", test))]
mod tests;
