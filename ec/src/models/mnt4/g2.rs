use core::ops::Neg;

use crate::{
    mnt4::MNT4Parameters,
    models::mnt4::MNT4,
    short_weierstrass::{Affine, Projective},
    AffineCurve,
};
use ark_ff::fields::{Field, Fp2};
use ark_std::vec::Vec;
use num_traits::One;

pub type G2Affine<P> = Affine<<P as MNT4Parameters>::G2Parameters>;
pub type G2Projective<P> = Projective<<P as MNT4Parameters>::G2Parameters>;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "P: MNT4Parameters"),
    Debug(bound = "P: MNT4Parameters"),
    PartialEq(bound = "P: MNT4Parameters"),
    Eq(bound = "P: MNT4Parameters")
)]
pub struct G2Prepared<P: MNT4Parameters> {
    pub x: Fp2<P::Fp2Config>,
    pub y: Fp2<P::Fp2Config>,
    pub x_over_twist: Fp2<P::Fp2Config>,
    pub y_over_twist: Fp2<P::Fp2Config>,
    pub double_coefficients: Vec<AteDoubleCoefficients<P>>,
    pub addition_coefficients: Vec<AteAdditionCoefficients<P>>,
}

impl<P: MNT4Parameters> Default for G2Prepared<P> {
    fn default() -> Self {
        Self::from(G2Affine::<P>::prime_subgroup_generator())
    }
}

impl<P: MNT4Parameters> From<G2Affine<P>> for G2Prepared<P> {
    fn from(g2: G2Affine<P>) -> Self {
        let twist_inv = P::TWIST.inverse().unwrap();

        let mut g2p = G2Prepared {
            x: g2.x,
            y: g2.y,
            x_over_twist: g2.x * &twist_inv,
            y_over_twist: g2.y * &twist_inv,
            double_coefficients: vec![],
            addition_coefficients: vec![],
        };

        let mut r = G2ProjectiveExtended {
            x: g2.x,
            y: g2.y,
            z: <Fp2<P::Fp2Config>>::one(),
            t: <Fp2<P::Fp2Config>>::one(),
        };

        let neg_g2 = g2.neg();
        for bit in P::ATE_LOOP_COUNT_2.iter().skip(1) {
            let (r2, coeff) = MNT4::<P>::doubling_step_for_flipped_miller_loop(&r);
            g2p.double_coefficients.push(coeff);
            r = r2;

            let add_coeff;
            let r_temp;
            match bit {
                1 => {
                    (r_temp, add_coeff) =
                        MNT4::<P>::mixed_addition_step_for_flipped_miller_loop(&g2.x, &g2.y, &r);
                },
                -1 => {
                    (r_temp, add_coeff) = MNT4::<P>::mixed_addition_step_for_flipped_miller_loop(
                        &neg_g2.x, &neg_g2.y, &r,
                    );
                },
                _ => continue,
            }
            g2p.addition_coefficients.push(add_coeff);
            r = r_temp;
        }

        if P::ATE_IS_LOOP_COUNT_NEG {
            let rz_inv = r.z.inverse().unwrap();
            let rz2_inv = rz_inv.square();
            let rz3_inv = rz_inv * &rz2_inv;

            let minus_r_affine_x = r.x * &rz2_inv;
            let minus_r_affine_y = -r.y * &rz3_inv;

            let add_result = MNT4::<P>::mixed_addition_step_for_flipped_miller_loop(
                &minus_r_affine_x,
                &minus_r_affine_y,
                &r,
            );
            g2p.addition_coefficients.push(add_result.1);
        }

        g2p
    }
}

pub(super) struct G2ProjectiveExtended<P: MNT4Parameters> {
    pub(crate) x: Fp2<P::Fp2Config>,
    pub(crate) y: Fp2<P::Fp2Config>,
    pub(crate) z: Fp2<P::Fp2Config>,
    pub(crate) t: Fp2<P::Fp2Config>,
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "P: MNT4Parameters"),
    Debug(bound = "P: MNT4Parameters"),
    PartialEq(bound = "P: MNT4Parameters"),
    Eq(bound = "P: MNT4Parameters")
)]
pub struct AteDoubleCoefficients<P: MNT4Parameters> {
    pub c_h: Fp2<P::Fp2Config>,
    pub c_4c: Fp2<P::Fp2Config>,
    pub c_j: Fp2<P::Fp2Config>,
    pub c_l: Fp2<P::Fp2Config>,
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "P: MNT4Parameters"),
    Debug(bound = "P: MNT4Parameters"),
    PartialEq(bound = "P: MNT4Parameters"),
    Eq(bound = "P: MNT4Parameters")
)]
pub struct AteAdditionCoefficients<P: MNT4Parameters> {
    pub c_l1: Fp2<P::Fp2Config>,
    pub c_rz: Fp2<P::Fp2Config>,
}
