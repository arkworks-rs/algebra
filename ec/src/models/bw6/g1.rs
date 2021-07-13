use crate::{
    bw6::BW6Parameters,
    short_weierstrass::{SWAffine, SWProjective},
};

pub type G1Affine<P> = SWAffine<<P as BW6Parameters>::G1Parameters>;
pub type G1Projective<P> = SWProjective<<P as BW6Parameters>::G1Parameters>;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "P: BW6Parameters"),
    Debug(bound = "P: BW6Parameters"),
    PartialEq(bound = "P: BW6Parameters"),
    Eq(bound = "P: BW6Parameters")
)]
pub struct G1Prepared<P: BW6Parameters>(pub G1Affine<P>);

impl<P: BW6Parameters> From<G1Affine<P>> for G1Prepared<P> {
    fn from(other: G1Affine<P>) -> Self {
        G1Prepared(other)
    }
}

impl<P: BW6Parameters> From<G1Projective<P>> for G1Prepared<P> {
    fn from(other: G1Projective<P>) -> Self {
        other.into()
    }
}

impl<P: BW6Parameters> G1Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<P: BW6Parameters> Default for G1Prepared<P> {
    fn default() -> Self {
        G1Prepared(G1Affine::<P>::generator())
    }
}
