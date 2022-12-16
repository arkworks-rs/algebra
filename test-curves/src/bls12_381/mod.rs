pub mod fr;
pub use fr::*;

#[cfg(feature = "bls12_381_curve")]
pub mod fq;
#[cfg(feature = "bls12_381_curve")]
pub mod fq12;
#[cfg(feature = "bls12_381_curve")]
pub mod fq2;
#[cfg(feature = "bls12_381_curve")]
pub mod fq6;
#[cfg(feature = "bls12_381_curve")]
pub mod g1;
#[cfg(feature = "bls12_381_curve")]
pub mod g1_swu_iso;
#[cfg(feature = "bls12_381_curve")]
pub mod g2;
#[cfg(feature = "bls12_381_curve")]
pub mod g2_swu_iso;
#[cfg(feature = "bls12_381_curve")]
pub use {fq::*, fq12::*, fq2::*, fq6::*, g1::*, g1_swu_iso::*, g2::*, g2_swu_iso::*};

#[cfg(test)]
mod tests;

#[cfg(feature = "bls12_381_curve")]
pub use pairing::*;
#[cfg(feature = "bls12_381_curve")]
mod pairing {
    use super::*;
    use ark_ec::bls12::{Bls12, Bls12Config, TwistType};

    pub type Bls12_381 = Bls12<Config>;

    pub struct Config;

    impl Bls12Config for Config {
        const X: &'static [u64] = &[0xd201000000010000];
        const X_IS_NEGATIVE: bool = true;
        const TWIST_TYPE: TwistType = TwistType::M;
        type Fp = Fq;
        type Fp2Config = Fq2Config;
        type Fp6Config = Fq6Config;
        type Fp12Config = Fq12Config;
        type G1Config = self::g1::Config;
        type G2Config = self::g2::Config;
    }

    pub type G1Prepared = ark_ec::bls12::G1Prepared<Config>;
    pub type G2Prepared = ark_ec::bls12::G2Prepared<Config>;
}
