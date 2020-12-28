use ark_ff::{Field, PrimeField, SquareRootField};
use crate::models::SWModelParameters;

pub trait ShallueVanDeWoestijneParams : SWModelParameters {
    // a non-zero element of F meeting the below criteria.
    // Let g(x) be the value of y^2, e.g. g(x) = x^3 + Ax + B
    // 1.  g(Z) != 0 in F.
    // 2.  -(3 * Z^2 + 4 * A) / (4 * g(Z)) != 0 in F.
    // 3.  -(3 * Z^2 + 4 * A) / (4 * g(Z)) is square in F.
    // 4.  At least one of g(Z) and g(-Z / 2) is square in F.
    const Z : Self::BaseField;
}

pub struct shallue_van_de_woestijne_hasher {
    pub domain: Vec<u8>,
}