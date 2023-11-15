use ark_ec::bls12::{Bls12, Bls12Config, TwistType};

use crate::{Fq, Fq12Config, Fq2Config, Fq6Config};

pub mod g1;
pub mod g2;
pub(crate) mod util;

mod g1_swu_iso;
mod g2_swu_iso;

#[cfg(test)]
mod tests;

pub use self::{
    g1::{G1Affine, G1Projective},
    g2::{G2Affine, G2Projective},
};

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
