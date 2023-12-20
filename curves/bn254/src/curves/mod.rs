use ark_ec::{
    bn,
    bn::{Bn, BnConfig, TwistType},
};
use ark_ff::MontFp;

use crate::*;

pub mod g1;
pub mod g2;

#[cfg(test)]
mod tests;

pub struct Config;

impl BnConfig for Config {
    const X: &'static [u64] = &[4965661367192848881];
    /// `x` is positive.
    const X_IS_NEGATIVE: bool = false;
    const ATE_LOOP_COUNT: &'static [i8] = &[
        0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0,
        0, 1, 1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0,
        -1, 0, 0, 1, 0, 1, 1,
    ];

    const TWIST_MUL_BY_Q_X: Fq2 = Fq2::new(
        MontFp!("21575463638280843010398324269430826099269044274347216827212613867836435027261"),
        MontFp!("10307601595873709700152284273816112264069230130616436755625194854815875713954"),
    );
    const TWIST_MUL_BY_Q_Y: Fq2 = Fq2::new(
        MontFp!("2821565182194536844548159561693502659359617185244120367078079554186484126554"),
        MontFp!("3505843767911556378687030309984248845540243509899259641013678093033130930403"),
    );
    const TWIST_TYPE: TwistType = TwistType::D;
    type Fp = Fq;
    type Fp2Config = Fq2Config;
    type Fp6Config = Fq6Config;
    type Fp12Config = Fq12Config;
    type G1Config = g1::Config;
    type G2Config = g2::Config;
}

pub type Bn254 = Bn<Config>;

pub type G1Affine = bn::G1Affine<Config>;
pub type G1Projective = bn::G1Projective<Config>;
pub type G2Affine = bn::G2Affine<Config>;
pub type G2Projective = bn::G2Projective<Config>;
