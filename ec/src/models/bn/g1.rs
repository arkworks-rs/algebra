use crate::{
    bn::BnConfig,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::*;
use educe::Educe;

pub type G1Affine<P> = Affine<<P as BnConfig>::G1Config>;
pub type G1Projective<P> = Projective<<P as BnConfig>::G1Config>;

#[derive(Educe, CanonicalSerialize, CanonicalDeserialize)]
#[educe(Clone, Debug, PartialEq, Eq)]
pub struct G1Prepared<P: BnConfig>(pub G1Affine<P>);

impl<P: BnConfig> From<G1Affine<P>> for G1Prepared<P> {
    fn from(other: G1Affine<P>) -> Self {
        Self(other)
    }
}

impl<P: BnConfig> From<G1Projective<P>> for G1Prepared<P> {
    fn from(q: G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<'a, P: BnConfig> From<&'a G1Affine<P>> for G1Prepared<P> {
    fn from(other: &'a G1Affine<P>) -> Self {
        Self(*other)
    }
}

impl<'a, P: BnConfig> From<&'a G1Projective<P>> for G1Prepared<P> {
    fn from(q: &'a G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: BnConfig> G1Prepared<P> {
    pub const fn is_zero(&self) -> bool {
        self.0.infinity
    }
}

impl<P: BnConfig> Default for G1Prepared<P> {
    fn default() -> Self {
        Self(G1Affine::<P>::generator())
    }
}
