use ark_ff::{Field, PrimeField};

pub mod bls12;
pub mod bn;
pub mod bw6;
pub mod mnt4;
pub mod mnt6;

pub mod short_weierstrass;
pub mod twisted_edwards;

/// Elliptic curves can be represented via different "models" with varying
/// efficiency properties.
/// `CurveConfig` bundles together the types that are common
/// to all models of the given curve, namely the `BaseField` over which the
/// curve is defined, and the `ScalarField` defined by the appropriate
/// prime-order subgroup of the curve.
pub trait CurveConfig: Send + Sync + Sized + 'static {
    /// Base field that the curve is defined over.
    type BaseField: Field;
    /// Finite prime field corresponding to an appropriate prime-order subgroup
    /// of the curve group.
    type ScalarField: PrimeField + Into<<Self::ScalarField as PrimeField>::BigInt>;

    /// The cofactor of this curve, represented as a sequence of little-endian limbs.
    const COFACTOR: &'static [u64];
    const COFACTOR_INV: Self::ScalarField;

    fn cofactor_is_one() -> bool {
        Self::COFACTOR[0] == 1 && Self::COFACTOR.iter().skip(1).all(|&e| e == 0)
    }
}
