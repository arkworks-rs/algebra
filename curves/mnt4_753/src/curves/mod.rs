use ark_ec::models::mnt4::{MNT4Config, MNT4};
use ark_ff::{biginteger::BigInteger768, AdditiveGroup, BigInt, Field, Fp2, MontFp};

use crate::{Fq, Fq2Config, Fq4Config, Fr};

pub mod g1;
pub mod g2;

#[cfg(test)]
mod tests;

pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};

pub type MNT4_753 = MNT4<Config>;

pub struct Config;

impl MNT4Config for Config {
    const TWIST: Fp2<Self::Fp2Config> = Fp2::new(Fq::ZERO, Fq::ONE);
    // A coefficient of MNT4-753 G2 =
    // ```
    // mnt4753_twist_coeff_a = mnt4753_Fq2(mnt4753_G1::coeff_a * non_residue, mnt6753_Fq::zero());
    //  = (A_COEFF * NONRESIDUE, ZERO)
    //  = (26, ZERO)
    // ```
    const TWIST_COEFF_A: Fp2<Self::Fp2Config> = Fp2::new(G1_COEFF_A_NON_RESIDUE, Fq::ZERO);
    // https://github.com/o1-labs/snarky/blob/9c21ab2bb23874604640740d646a932e813432c3/snarkette/mnt4753.ml
    const ATE_LOOP_COUNT: &'static [i8] = &[
        1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 1, 0, 0, 0, -1, 0,
        -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 1, 0, -1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1,
        0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, -1, 0,
        0, -1, 0, 1, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, 0,
        0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1,
        0, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 0, -1,
        0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 0,
        -1, 0, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
        -1, 0, 0, 0, 1, 0, -1, 0, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, -1, 0, -1, 0, -1, 0,
        0, 0, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 0, 1,
        0, -1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0, 0,
        0, -1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0,
        0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0,
    ];
    const ATE_IS_LOOP_COUNT_NEG: bool = true;
    const FINAL_EXPONENT_LAST_CHUNK_1: BigInteger768 = BigInt!("0x1");
    const FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG: bool = true;
    // https://github.com/o1-labs/snarky/blob/9c21ab2bb23874604640740d646a932e813432c3/snarkette/mnt4753.ml#L100
    const FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0: BigInteger768 = BigInt!("204691208819330962009469868104636132783269696790011977400223898462431810102935615891307667367766898917669754470399");
    type Fp = Fq;
    type Fr = Fr;
    type Fp2Config = Fq2Config;
    type Fp4Config = Fq4Config;
    type G1Config = self::g1::Config;
    type G2Config = self::g2::Config;
}

// 26
pub const G1_COEFF_A_NON_RESIDUE: Fq = MontFp!("26");
