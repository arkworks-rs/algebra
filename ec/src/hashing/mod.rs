use crate::CurveGroup;
use ark_std::string::String;
use core::fmt;

pub mod curve_maps;
pub mod map_to_curve_hasher;

/// Trait for hashing arbitrary data to a group element on an elliptic curve
pub trait HashToCurve<T: CurveGroup>: Sized {
    /// Create a new hash to curve instance, with a given domain.
    fn new(domain: &[u8]) -> Result<Self, HashToCurveError>;

    /// Produce a hash of the message, which also depends on the domain.
    /// The output of the hash is a curve point in the prime order subgroup
    /// of the given elliptic curve.
    fn hash(&self, message: &[u8]) -> Result<T::Affine, HashToCurveError>;
}

/// This is an error that could occur during the hash to curve process
#[derive(Clone, Debug)]
pub enum HashToCurveError {
    /// Curve choice is unsupported by the given HashToCurve method.
    UnsupportedCurveError(String),

    /// Error with map to curve
    MapToCurveError(String),
}

impl ark_std::error::Error for HashToCurveError {}

impl fmt::Display for HashToCurveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            HashToCurveError::UnsupportedCurveError(s) => write!(f, "{}", s),
            HashToCurveError::MapToCurveError(s) => write!(f, "{}", s),
        }
    }
}

#[cfg(test)]
mod tests;
