use crate::{
    bls12::Bls12Parameters,
    short_weierstrass::{SWAffine, SWProjective},
};

pub type G1Affine<P> = SWAffine<<P as Bls12Parameters>::G1Parameters>;
pub type G1Projective<P> = SWProjective<<P as Bls12Parameters>::G1Parameters>;

#[derive(Derivative)]
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
    fn from(other: G1Projective<P>) -> Self {
        G1Prepared(other.into())
    }
}

impl<P: Bls12Parameters> G1Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<P: Bls12Parameters> Default for G1Prepared<P> {
    fn default() -> Self {
        G1Prepared(G1Affine::<P>::generator())
    }
}