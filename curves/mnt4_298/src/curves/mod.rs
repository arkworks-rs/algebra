use ark_ec::models::mnt4::{MNT4Config, MNT4};
use ark_ff::{biginteger::BigInteger320, AdditiveGroup, BigInt, Field, MontFp};

use crate::{Fq, Fq2, Fq2Config, Fq4Config, Fr};

pub mod g1;
pub mod g2;

#[cfg(test)]
mod tests;

pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};

pub type MNT4_298 = MNT4<Config>;

pub struct Config;

impl MNT4Config for Config {
    const TWIST: Fq2 = Fq2::new(Fq::ZERO, Fq::ONE);
    // A coefficient of MNT4-298 G2 =
    // ```
    // mnt4298_twist_coeff_a = mnt4298_Fq2(mnt4298_G1::coeff_a * non_residue, mnt6298_Fq::zero());
    //  = (A_COEFF * NONRESIDUE, ZERO)
    //  = (34, ZERO)
    // ```
    const TWIST_COEFF_A: Fq2 = Fq2::new(G1_COEFF_A_NON_RESIDUE, Fq::ZERO);

    // https://github.com/o1-labs/snarky/blob/9c21ab2bb23874604640740d646a932e813432c3/snarkette/mnt4_80.ml#L88
    const ATE_LOOP_COUNT: &'static [i8] = &[
        1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, -1,
        0, 1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, -1, 0, -1, 0,
        0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, -1,
        0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1,
        0, -1, 0, 1, 0, 0, -1, 0, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0,
    ];
    const ATE_IS_LOOP_COUNT_NEG: bool = false;
    const FINAL_EXPONENT_LAST_CHUNK_1: BigInteger320 = BigInt!("0x1");
    const FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG: bool = false;
    // https://github.com/o1-labs/snarky/blob/9c21ab2bb23874604640740d646a932e813432c3/snarkette/mnt4_80.ml#L96
    const FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0: BigInteger320 =
        BigInt!("689871209842287392837045615510547309923794945");
    type Fp = Fq;
    type Fr = Fr;
    type Fp2Config = Fq2Config;
    type Fp4Config = Fq4Config;
    type G1Config = self::g1::Config;
    type G2Config = self::g2::Config;
}

// 34
pub const G1_COEFF_A_NON_RESIDUE: Fq = MontFp!("34");
