use core::ops::Neg;

use crate::{
    mnt6::MNT6Parameters,
    models::mnt6::MNT6,
    short_weierstrass::{Affine, Projective},
    AffineCurve,
};
use ark_ff::fields::{Field, Fp3};
use ark_std::vec::Vec;
use num_traits::One;

pub type G2Affine<P> = Affine<<P as MNT6Parameters>::G2Parameters>;
pub type G2Projective<P> = Projective<<P as MNT6Parameters>::G2Parameters>;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "P: MNT6Parameters"),
    Debug(bound = "P: MNT6Parameters"),
    PartialEq(bound = "P: MNT6Parameters"),
    Eq(bound = "P: MNT6Parameters")
)]
pub struct G2Prepared<P: MNT6Parameters> {
    pub x: Fp3<P::Fp3Config>,
    pub y: Fp3<P::Fp3Config>,
    pub x_over_twist: Fp3<P::Fp3Config>,
    pub y_over_twist: Fp3<P::Fp3Config>,
    pub double_coefficients: Vec<AteDoubleCoefficients<P>>,
    pub addition_coefficients: Vec<AteAdditionCoefficients<P>>,
}

impl<P: MNT6Parameters> Default for G2Prepared<P> {
    fn default() -> Self {
        Self::from(G2Affine::<P>::prime_subgroup_generator())
    }
}

impl<P: MNT6Parameters> From<G2Affine<P>> for G2Prepared<P> {
    fn from(g: G2Affine<P>) -> Self {
        let twist_inv = P::TWIST.inverse().unwrap();

        let mut g_prep = G2Prepared {
            x: g.x,
            y: g.y,
            x_over_twist: g.x * &twist_inv,
            y_over_twist: g.y * &twist_inv,
            double_coefficients: vec![],
            addition_coefficients: vec![],
        };

        let mut r = G2ProjectiveExtended {
            x: g.x,
            y: g.y,
            z: <Fp3<P::Fp3Config>>::one(),
            t: <Fp3<P::Fp3Config>>::one(),
        };

        let neg_g = g.neg();
        for bit in P::ATE_LOOP_COUNT.iter().skip(1) {
            let (r2, coeff) = MNT6::<P>::doubling_for_flipped_miller_loop(&r);
            g_prep.double_coefficients.push(coeff);
            r = r2;

            let (r_temp, add_coeff) = match bit {
                1 => MNT6::<P>::mixed_addition_for_flipper_miller_loop(&g.x, &g.y, &r),
                -1 => MNT6::<P>::mixed_addition_for_flipper_miller_loop(&neg_g.x, &neg_g.y, &r),
                0 => continue,
                _ => unreachable!(),
            };
            g_prep.addition_coefficients.push(add_coeff);
            r = r_temp;
        }

        if P::ATE_IS_LOOP_COUNT_NEG {
            let rz_inv = r.z.inverse().unwrap();
            let rz2_inv = rz_inv.square();
            let rz3_inv = rz_inv * &rz2_inv;

            let minus_r_x = r.x * &rz2_inv;
            let minus_r_y = -r.y * &rz3_inv;

            let add_result =
                MNT6::<P>::mixed_addition_for_flipper_miller_loop(&minus_r_x, &minus_r_y, &r);
            g_prep.addition_coefficients.push(add_result.1);
        }

        g_prep
    }
}

pub(super) struct G2ProjectiveExtended<P: MNT6Parameters> {
    pub(crate) x: Fp3<P::Fp3Config>,
    pub(crate) y: Fp3<P::Fp3Config>,
    pub(crate) z: Fp3<P::Fp3Config>,
    pub(crate) t: Fp3<P::Fp3Config>,
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "P: MNT6Parameters"),
    Debug(bound = "P: MNT6Parameters"),
    PartialEq(bound = "P: MNT6Parameters"),
    Eq(bound = "P: MNT6Parameters")
)]
pub struct AteDoubleCoefficients<P: MNT6Parameters> {
    pub c_h: Fp3<P::Fp3Config>,
    pub c_4c: Fp3<P::Fp3Config>,
    pub c_j: Fp3<P::Fp3Config>,
    pub c_l: Fp3<P::Fp3Config>,
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "P: MNT6Parameters"),
    Debug(bound = "P: MNT6Parameters"),
    PartialEq(bound = "P: MNT6Parameters"),
    Eq(bound = "P: MNT6Parameters")
)]
pub struct AteAdditionCoefficients<P: MNT6Parameters> {
    pub c_l1: Fp3<P::Fp3Config>,
    pub c_rz: Fp3<P::Fp3Config>,
}
