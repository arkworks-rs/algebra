use ark_ec::{
    models::mnt6::{MNT6Config, MNT6},
    short_weierstrass::SWCurveConfig,
};
use ark_ff::{biginteger::BigInteger320, AdditiveGroup, BigInt, Field, Fp3};

use crate::{Fq, Fq3Config, Fq6Config, Fr};

pub mod g1;
pub mod g2;

#[cfg(test)]
mod tests;

pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};

pub type MNT6_298 = MNT6<Config>;

pub struct Config;

impl MNT6Config for Config {
    const TWIST: Fp3<Self::Fp3Config> = Fp3::<Self::Fp3Config>::new(Fq::ZERO, Fq::ONE, Fq::ZERO);
    const TWIST_COEFF_A: Fp3<Self::Fp3Config> =
        Fp3::<Self::Fp3Config>::new(Fq::ZERO, Fq::ZERO, g1::Config::COEFF_A);

    // https://github.com/o1-labs/snarky/blob/9c21ab2bb23874604640740d646a932e813432c3/snarkette/mnt6_80.ml#L118
    const ATE_LOOP_COUNT: &'static [i8] = &[
        1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, -1,
        0, 1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, -1, 0, -1, 0,
        0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, -1,
        0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1,
        0, -1, 0, 1, 0, 0, -1, 0, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0,
    ];
    const ATE_IS_LOOP_COUNT_NEG: bool = true;
    const FINAL_EXPONENT_LAST_CHUNK_1: BigInteger320 = BigInt!("0x1");
    const FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG: bool = true;
    // https://github.com/o1-labs/snarky/blob/9c21ab2bb23874604640740d646a932e813432c3/snarkette/mnt6_80.ml#L126
    const FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0: BigInteger320 =
        BigInt!("689871209842287392837045615510547309923794944");
    type Fp = Fq;
    type Fr = Fr;
    type Fp3Config = Fq3Config;
    type Fp6Config = Fq6Config;
    type G1Config = self::g1::Config;
    type G2Config = self::g2::Config;
}
