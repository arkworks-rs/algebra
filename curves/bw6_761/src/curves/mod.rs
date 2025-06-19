use ark_ec::{
    bw6,
    bw6::{BW6Config, TwistType, BW6},
};
use ark_ff::{
    biginteger::BigInteger768 as BigInteger, fp6_2over3::Fp6, BigInt, CyclotomicMultSubgroup, Field,
};

use crate::*;

pub mod g1;
pub mod g2;

#[cfg(test)]
mod tests;

#[derive(PartialEq, Eq)]
pub struct Config;

impl BW6Config for Config {
    const X: BigInteger = BigInt!("0x8508c00000000001");
    /// `x` is positive.
    const X_IS_NEGATIVE: bool = false;
    // X
    const ATE_LOOP_COUNT_1: &'static [u64] = &[0x8508c00000000001];
    // (X-1)/3
    const X_MINUS_1_DIV_3: BigInteger = BigInt!("0x2c58400000000000");
    // X+1
    const ATE_LOOP_COUNT_1_IS_NEGATIVE: bool = false;
    // X^2-X-1
    const ATE_LOOP_COUNT_2: &'static [i8] = &[
        -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0,
        0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0,
        0, 1, 0, 1, 0, 0, 0, 1,
    ];
    const ATE_LOOP_COUNT_2_IS_NEGATIVE: bool = false;
    const TWIST_TYPE: TwistType = TwistType::M;
    const H_T: i64 = 13;
    const H_Y: i64 = 9;
    const T_MOD_R_IS_ZERO: bool = false;
    type Fp = Fq;
    type Fp3Config = Fq3Config;
    type Fp6Config = Fq6Config;
    type G1Config = g1::Config;
    type G2Config = g2::Config;

    fn final_exponentiation_hard_part(f: &Fp6<Self::Fp6Config>) -> Fp6<Self::Fp6Config> {
        // hard_part
        // From https://eprint.iacr.org/2020/351.pdf, Alg.6

        // R0(x) := (-103*x^7 + 70*x^6 + 269*x^5 - 197*x^4 - 314*x^3 - 73*x^2 - 263*x - 220)
        // R1(x) := (103*x^9 - 276*x^8 + 77*x^7 + 492*x^6 - 445*x^5 - 65*x^4 + 452*x^3 - 181*x^2 + 34*x + 229)
        // f ^ R0(u) * (f ^ q) ^ R1(u) in a 2-NAF multi-exp fashion.

        // steps 1,2,3
        let f0 = *f;
        let mut f0p = f0;
        f0p.frobenius_map_in_place(1);
        let f1 = Self::exp_by_x(&f0);
        let mut f1p = f1;
        f1p.frobenius_map_in_place(1);
        let f2 = Self::exp_by_x(&f1);
        let mut f2p = f2;
        f2p.frobenius_map_in_place(1);
        let f3 = Self::exp_by_x(&f2);
        let mut f3p = f3;
        f3p.frobenius_map_in_place(1);
        let f4 = Self::exp_by_x(&f3);
        let mut f4p = f4;
        f4p.frobenius_map_in_place(1);
        let f5 = Self::exp_by_x(&f4);
        let mut f5p = f5;
        f5p.frobenius_map_in_place(1);
        let f6 = Self::exp_by_x(&f5);
        let mut f6p = f6;
        f6p.frobenius_map_in_place(1);
        let f7 = Self::exp_by_x(&f6);
        let mut f7p = f7;
        f7p.frobenius_map_in_place(1);

        // step 4
        let f8p = Self::exp_by_x(&f7p);
        let f9p = Self::exp_by_x(&f8p);

        // step 5
        let mut f5p_p3 = f5p;
        f5p_p3.cyclotomic_inverse_in_place();
        let result1 = f3p * &f6p * &f5p_p3;

        // step 6
        let result2 = result1.square();
        let f4_2p = f4 * &f2p;
        let mut tmp1_p3 = f0 * &f1 * &f3 * &f4_2p * &f8p;
        tmp1_p3.cyclotomic_inverse_in_place();
        let result3 = result2 * &f5 * &f0p * &tmp1_p3;

        // step 7
        let result4 = result3.square();
        let mut f7_p3 = f7;
        f7_p3.cyclotomic_inverse_in_place();
        let result5 = result4 * &f9p * &f7_p3;

        // step 8
        let result6 = result5.square();
        let f2_4p = f2 * &f4p;
        let f4_2p_5p = f4_2p * &f5p;
        let mut tmp2_p3 = f2_4p * &f3 * &f3p;
        tmp2_p3.cyclotomic_inverse_in_place();
        let result7 = result6 * &f4_2p_5p * &f6 * &f7p * &tmp2_p3;

        // step 9
        let result8 = result7.square();
        let mut tmp3_p3 = f0p * &f9p;
        tmp3_p3.cyclotomic_inverse_in_place();
        let result9 = result8 * &f0 * &f7 * &f1p * &tmp3_p3;

        // step 10
        let result10 = result9.square();
        let f6p_8p = f6p * &f8p;
        let f5_7p = f5 * &f7p;
        let mut tmp4_p3 = f6p_8p;
        tmp4_p3.cyclotomic_inverse_in_place();
        let result11 = result10 * &f5_7p * &f2p * &tmp4_p3;

        // step 11
        let result12 = result11.square();
        let f3_6 = f3 * &f6;
        let f1_7 = f1 * &f7;
        let mut tmp5_p3 = f1_7 * &f2;
        tmp5_p3.cyclotomic_inverse_in_place();
        let result13 = result12 * &f3_6 * &f9p * &tmp5_p3;

        // step 12
        let result14 = result13.square();
        let mut tmp6_p3 = f4_2p * &f5_7p * &f6p_8p;
        tmp6_p3.cyclotomic_inverse_in_place();
        let result15 = result14 * &f0 * &f0p * &f3p * &f5p * &tmp6_p3;

        // step 13
        let result16 = result15.square();
        let mut tmp7_p3 = f3_6;
        tmp7_p3.cyclotomic_inverse_in_place();
        let result17 = result16 * &f1p * &tmp7_p3;

        // step 14
        let result18 = result17.square();
        let mut tmp8_p3 = f2_4p * &f4_2p_5p * &f9p;
        tmp8_p3.cyclotomic_inverse_in_place();
        let result19 = result18 * &f1_7 * &f5_7p * &f0p * &tmp8_p3;

        result19
    }
}

pub type BW6_761 = BW6<Config>;

pub type G1Affine = bw6::G1Affine<Config>;
pub type G1Projective = bw6::G1Projective<Config>;
pub type G2Affine = bw6::G2Affine<Config>;
pub type G2Projective = bw6::G2Projective<Config>;
