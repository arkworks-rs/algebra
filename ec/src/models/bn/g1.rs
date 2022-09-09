use crate::{
    bn::BnParameters,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};
use ark_serialize::*;
use ark_std::vec::Vec;

pub type G1Affine<P> = Affine<<P as BnParameters>::G1Parameters>;
pub type G1Projective<P> = Projective<<P as BnParameters>::G1Parameters>;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Clone(bound = "P: BnParameters"),
    Debug(bound = "P: BnParameters"),
    PartialEq(bound = "P: BnParameters"),
    Eq(bound = "P: BnParameters")
)]
pub struct G1Prepared<P: BnParameters>(pub G1Affine<P>);

impl<P: BnParameters> From<G1Affine<P>> for G1Prepared<P> {
    fn from(other: G1Affine<P>) -> Self {
        G1Prepared(other)
    }
}

impl<P: BnParameters> From<G1Projective<P>> for G1Prepared<P> {
    fn from(q: G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<'a, P: BnParameters> From<&'a G1Affine<P>> for G1Prepared<P> {
    fn from(other: &'a G1Affine<P>) -> Self {
        G1Prepared(*other)
    }
}

impl<'a, P: BnParameters> From<&'a G1Projective<P>> for G1Prepared<P> {
    fn from(q: &'a G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: BnParameters> G1Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.0.infinity
    }
}

impl<P: BnParameters> Default for G1Prepared<P> {
    fn default() -> Self {
        G1Prepared(G1Affine::<P>::generator())
    }
}
