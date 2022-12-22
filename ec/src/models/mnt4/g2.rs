use ark_std::ops::Neg;

use crate::{
    mnt4::MNT4Config,
    models::mnt4::MNT4,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};
use ark_ff::fields::{Field, Fp2};
use ark_serialize::*;
use ark_std::vec::Vec;
use num_traits::One;

pub type G2Affine<P> = Affine<<P as MNT4Config>::G2Config>;
pub type G2Projective<P> = Projective<<P as MNT4Config>::G2Config>;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Clone(bound = "P: MNT4Config"),
    Debug(bound = "P: MNT4Config"),
    PartialEq(bound = "P: MNT4Config"),
    Eq(bound = "P: MNT4Config")
)]
pub struct G2Prepared<P: MNT4Config> {
    pub x: Fp2<P::Fp2Config>,
    pub y: Fp2<P::Fp2Config>,
    pub x_over_twist: Fp2<P::Fp2Config>,
    pub y_over_twist: Fp2<P::Fp2Config>,
    pub double_coefficients: Vec<AteDoubleCoefficients<P>>,
    pub addition_coefficients: Vec<AteAdditionCoefficients<P>>,
}

impl<P: MNT4Config> Default for G2Prepared<P> {
    fn default() -> Self {
        Self::from(G2Affine::<P>::generator())
    }
}

impl<P: MNT4Config> From<G2Affine<P>> for G2Prepared<P> {
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
            z: <Fp2<P::Fp2Config>>::one(),
            t: <Fp2<P::Fp2Config>>::one(),
        };

        let neg_g = g.neg();
        for bit in P::ATE_LOOP_COUNT.iter().skip(1) {
            let (r2, coeff) = MNT4::<P>::doubling_for_flipped_miller_loop(&r);
            g_prep.double_coefficients.push(coeff);
            r = r2;

            let (r_temp, add_coeff) = match bit {
                1 => MNT4::<P>::mixed_addition_for_flipped_miller_loop(&g.x, &g.y, &r),
                -1 => MNT4::<P>::mixed_addition_for_flipped_miller_loop(&neg_g.x, &neg_g.y, &r),
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

            let minus_r_affine_x = r.x * &rz2_inv;
            let minus_r_affine_y = -r.y * &rz3_inv;

            let add_result = MNT4::<P>::mixed_addition_for_flipped_miller_loop(
                &minus_r_affine_x,
                &minus_r_affine_y,
                &r,
            );
            g_prep.addition_coefficients.push(add_result.1);
        }

        g_prep
    }
}

impl<'a, P: MNT4Config> From<&'a G2Affine<P>> for G2Prepared<P> {
    fn from(g2: &'a G2Affine<P>) -> Self {
        (*g2).into()
    }
}

impl<P: MNT4Config> From<G2Projective<P>> for G2Prepared<P> {
    fn from(g2: G2Projective<P>) -> Self {
        g2.into_affine().into()
    }
}
impl<'a, P: MNT4Config> From<&'a G2Projective<P>> for G2Prepared<P> {
    fn from(g2: &'a G2Projective<P>) -> Self {
        (*g2).into()
    }
}

pub(super) struct G2ProjectiveExtended<P: MNT4Config> {
    pub(crate) x: Fp2<P::Fp2Config>,
    pub(crate) y: Fp2<P::Fp2Config>,
    pub(crate) z: Fp2<P::Fp2Config>,
    pub(crate) t: Fp2<P::Fp2Config>,
}

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Clone(bound = "P: MNT4Config"),
    Debug(bound = "P: MNT4Config"),
    PartialEq(bound = "P: MNT4Config"),
    Eq(bound = "P: MNT4Config")
)]
pub struct AteDoubleCoefficients<P: MNT4Config> {
    pub c_h: Fp2<P::Fp2Config>,
    pub c_4c: Fp2<P::Fp2Config>,
    pub c_j: Fp2<P::Fp2Config>,
    pub c_l: Fp2<P::Fp2Config>,
}

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Clone(bound = "P: MNT4Config"),
    Debug(bound = "P: MNT4Config"),
    PartialEq(bound = "P: MNT4Config"),
    Eq(bound = "P: MNT4Config")
)]
pub struct AteAdditionCoefficients<P: MNT4Config> {
    pub c_l1: Fp2<P::Fp2Config>,
    pub c_rz: Fp2<P::Fp2Config>,
}
