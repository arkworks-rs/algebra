use crate::{
    mnt6::MNT6Config,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};
use ark_ff::Fp3;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::*;
use educe::Educe;

pub type G1Affine<P> = Affine<<P as MNT6Config>::G1Config>;
pub type G1Projective<P> = Projective<<P as MNT6Config>::G1Config>;

#[derive(Educe, CanonicalSerialize, CanonicalDeserialize)]
#[educe(Copy, Clone, Debug, PartialEq, Eq)]
pub struct G1Prepared<P: MNT6Config> {
    pub x: P::Fp,
    pub y: P::Fp,
    pub x_twist: Fp3<P::Fp3Config>,
    pub y_twist: Fp3<P::Fp3Config>,
}

impl<P: MNT6Config> From<G1Affine<P>> for G1Prepared<P> {
    fn from(g1: G1Affine<P>) -> Self {
        let mut x_twist = P::TWIST;
        x_twist.mul_assign_by_fp(&g1.x);

        let mut y_twist = P::TWIST;
        y_twist.mul_assign_by_fp(&g1.y);

        Self {
            x: g1.x,
            y: g1.y,
            x_twist,
            y_twist,
        }
    }
}

impl<'a, P: MNT6Config> From<&'a G1Affine<P>> for G1Prepared<P> {
    fn from(g1: &'a G1Affine<P>) -> Self {
        (*g1).into()
    }
}

impl<P: MNT6Config> From<G1Projective<P>> for G1Prepared<P> {
    fn from(g1: G1Projective<P>) -> Self {
        g1.into_affine().into()
    }
}
impl<'a, P: MNT6Config> From<&'a G1Projective<P>> for G1Prepared<P> {
    fn from(g1: &'a G1Projective<P>) -> Self {
        (*g1).into()
    }
}

impl<P: MNT6Config> Default for G1Prepared<P> {
    fn default() -> Self {
        Self::from(G1Affine::<P>::generator())
    }
}
