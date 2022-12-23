use crate::{
    mnt4::MNT4Config,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};
use ark_ff::Fp2;
use ark_serialize::*;
use ark_std::vec::Vec;

pub type G1Affine<P> = Affine<<P as MNT4Config>::G1Config>;
pub type G1Projective<P> = Projective<<P as MNT4Config>::G1Config>;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Copy(bound = "P: MNT4Config"),
    Clone(bound = "P: MNT4Config"),
    Debug(bound = "P: MNT4Config"),
    PartialEq(bound = "P: MNT4Config"),
    Eq(bound = "P: MNT4Config")
)]
pub struct G1Prepared<P: MNT4Config> {
    pub x: P::Fp,
    pub y: P::Fp,
    pub x_twist: Fp2<P::Fp2Config>,
    pub y_twist: Fp2<P::Fp2Config>,
}

impl<P: MNT4Config> From<G1Affine<P>> for G1Prepared<P> {
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

impl<'a, P: MNT4Config> From<&'a G1Affine<P>> for G1Prepared<P> {
    fn from(g1: &'a G1Affine<P>) -> Self {
        (*g1).into()
    }
}

impl<P: MNT4Config> From<G1Projective<P>> for G1Prepared<P> {
    fn from(g1: G1Projective<P>) -> Self {
        g1.into_affine().into()
    }
}
impl<'a, P: MNT4Config> From<&'a G1Projective<P>> for G1Prepared<P> {
    fn from(g1: &'a G1Projective<P>) -> Self {
        (*g1).into()
    }
}

impl<P: MNT4Config> Default for G1Prepared<P> {
    fn default() -> Self {
        Self::from(G1Affine::<P>::generator())
    }
}
