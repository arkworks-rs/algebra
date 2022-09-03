use crate::{
    bls12::Bls12Parameters,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};
use ark_serialize::*;
use ark_std::vec::Vec;

pub type G1Affine<P> = Affine<<P as Bls12Parameters>::G1Parameters>;
pub type G1Projective<P> = Projective<<P as Bls12Parameters>::G1Parameters>;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Clone(bound = "P: Bls12Parameters"),
    Debug(bound = "P: Bls12Parameters"),
    PartialEq(bound = "P: Bls12Parameters"),
    Eq(bound = "P: Bls12Parameters")
)]
pub struct G1Prepared<P: Bls12Parameters>(pub G1Affine<P>);

impl<P: Bls12Parameters> From<G1Affine<P>> for G1Prepared<P> {
    fn from(other: G1Affine<P>) -> Self {
        G1Prepared(other)
    }
}

impl<P: Bls12Parameters> From<G1Projective<P>> for G1Prepared<P> {
    fn from(q: G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<'a, P: Bls12Parameters> From<&'a G1Affine<P>> for G1Prepared<P> {
    fn from(other: &'a G1Affine<P>) -> Self {
        G1Prepared(*other)
    }
}

impl<'a, P: Bls12Parameters> From<&'a G1Projective<P>> for G1Prepared<P> {
    fn from(q: &'a G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: Bls12Parameters> G1Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.0.is_identity()
    }
}

impl<P: Bls12Parameters> Default for G1Prepared<P> {
    fn default() -> Self {
        G1Prepared(G1Affine::<P>::generator())
    }
}
