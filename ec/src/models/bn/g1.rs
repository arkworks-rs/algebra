use crate::{
    bn::BnParameters,
    short_weierstrass_jacobian::{SWAffine, SWProjective},
};

pub type G1Affine<P> = SWAffine<<P as BnParameters>::G1Parameters>;
pub type G1Projective<P> = SWProjective<<P as BnParameters>::G1Parameters>;

#[derive(Derivative)]
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
    fn from(other: G1Projective<P>) -> Self {
        G1Prepared(other.into())
    }
}

impl<P: BnParameters> G1Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<P: BnParameters> Default for G1Prepared<P> {
    fn default() -> Self {
        G1Prepared(G1Affine::<P>::generator())
    }
}
