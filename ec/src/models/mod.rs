use ark_ff::{Field, PrimeField, SquareRootField};

pub mod bls12;
pub mod bn;
pub mod bw6;
pub mod mnt4;
pub mod mnt6;
pub mod short_weierstrass_jacobian;
pub mod twisted_edwards_extended;

pub use {
    short_weierstrass_jacobian::SWModelParameters,
    twisted_edwards_extended::{MontgomeryModelParameters, TEModelParameters},
};

pub trait ModelParameters: Send + Sync + 'static {
    type BaseField: Field + SquareRootField;
    type ScalarField: PrimeField
        + SquareRootField
        + From<<Self::ScalarField as PrimeField>::BigInt>
        + Into<<Self::ScalarField as PrimeField>::BigInt>;
}
