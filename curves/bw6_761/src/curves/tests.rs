use crate::*;
use ark_algebra_test_templates::*;
use ark_ff::Field;

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<BW6_761>; msm);
test_pairing!(pairing; crate::BW6_761);
test_group!(g1_glv; G1Projective; glv);
test_group!(g2_glv; G2Projective; glv);

#[test]
fn test_pairing_with_leading_zero_limb_in_ate_loop_count_1() {
    use ark_ec::{
        bw6::{BW6Config, TwistType, BW6},
        pairing::Pairing,
    };
    use ark_ff::fp6_2over3::Fp6;
    use ark_std::UniformRand;

    // Same parameters as BW6-761, with a zero high limb added to `ATE_LOOP_COUNT_1`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct PaddedLoopCountConfig;
    impl BW6Config for PaddedLoopCountConfig {
        const X: <Fq as ark_ff::PrimeField>::BigInt = <Config as BW6Config>::X;
        const X_IS_NEGATIVE: bool = <Config as BW6Config>::X_IS_NEGATIVE;
        const ATE_LOOP_COUNT_1: &'static [u64] = &[0x8508c00000000001, 0];
        const X_MINUS_1_DIV_3: <Fq as ark_ff::PrimeField>::BigInt =
            <Config as BW6Config>::X_MINUS_1_DIV_3;
        const ATE_LOOP_COUNT_1_IS_NEGATIVE: bool =
            <Config as BW6Config>::ATE_LOOP_COUNT_1_IS_NEGATIVE;
        const ATE_LOOP_COUNT_2: &'static [i8] = <Config as BW6Config>::ATE_LOOP_COUNT_2;
        const ATE_LOOP_COUNT_2_IS_NEGATIVE: bool =
            <Config as BW6Config>::ATE_LOOP_COUNT_2_IS_NEGATIVE;
        const TWIST_TYPE: TwistType = <Config as BW6Config>::TWIST_TYPE;
        const H_T: i64 = <Config as BW6Config>::H_T;
        const H_Y: i64 = <Config as BW6Config>::H_Y;
        const T_MOD_R_IS_ZERO: bool = <Config as BW6Config>::T_MOD_R_IS_ZERO;
        type Fp = Fq;
        type Fp3Config = Fq3Config;
        type Fp6Config = Fq6Config;
        type G1Config = crate::g1::Config;
        type G2Config = crate::g2::Config;

        fn final_exponentiation_hard_part(f: &Fp6<Fq6Config>) -> Fp6<Fq6Config> {
            <Config as BW6Config>::final_exponentiation_hard_part(f)
        }
    }

    let mut rng = ark_std::test_rng();
    let p = G1Projective::rand(&mut rng);
    let q = G2Projective::rand(&mut rng);
    assert_eq!(
        BW6::<PaddedLoopCountConfig>::pairing(p, q).0,
        BW6_761::pairing(p, q).0
    );
}
