use crate::{
    bw6::BW6Config,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::*;
use educe::Educe;

pub type G1Affine<P> = Affine<<P as BW6Config>::G1Config>;
pub type G1Projective<P> = Projective<<P as BW6Config>::G1Config>;

#[derive(Educe, CanonicalSerialize, CanonicalDeserialize)]
#[educe(Copy, Clone, Debug, PartialEq, Eq)]
pub struct G1Prepared<P: BW6Config>(pub G1Affine<P>);

impl<P: BW6Config> From<G1Affine<P>> for G1Prepared<P> {
    fn from(other: G1Affine<P>) -> Self {
        Self(other)
    }
}

impl<P: BW6Config> From<G1Projective<P>> for G1Prepared<P> {
    fn from(q: G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<'a, P: BW6Config> From<&'a G1Affine<P>> for G1Prepared<P> {
    fn from(other: &'a G1Affine<P>) -> Self {
        Self(*other)
    }
}

impl<'a, P: BW6Config> From<&'a G1Projective<P>> for G1Prepared<P> {
    fn from(q: &'a G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: BW6Config> G1Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<P: BW6Config> Default for G1Prepared<P> {
    fn default() -> Self {
        Self(G1Affine::<P>::generator())
    }
}
