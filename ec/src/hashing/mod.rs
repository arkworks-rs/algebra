use crate::AffineCurve;
use ark_std::string::String;
use core::fmt;

pub mod curve_maps;
pub mod map_to_curve_hasher;

pub mod field_hashers;

/// Trait for hashing arbitrary data to a group element on an elliptic curve
pub trait HashToCurve<T: AffineCurve>: Sized {
    /// Create a new hash to curve instance, with a given domain.
    fn new(domain: &[u8]) -> Result<Self, HashToCurveError>;

    /// Produce a hash of the message, which also depends on the domain.
    /// The output of the hash is a curve point in the prime order subgroup
    /// of the given elliptic curve.
    fn hash(&self, message: &[u8]) -> Result<T, HashToCurveError>;
}

/// This is an error that could occur during the hash to curve process
#[derive(Clone, Debug)]
pub enum HashToCurveError {
    /// Curve choice is unsupported by the given HashToCurve method.
    UnsupportedCurveError(String),

    /// Error in domain choice
    DomainError(String),

    /// Error while hashing
    HashingError(String),

    /// Error with map to curve
    MapToCurveError(String),

    /// Error with hash to field
    HashToFieldError(String),
}

impl ark_std::error::Error for HashToCurveError {}

impl fmt::Display for HashToCurveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            HashToCurveError::DomainError(s) => write!(f, "{}", s),
            HashToCurveError::UnsupportedCurveError(s) => write!(f, "{}", s),
            HashToCurveError::HashingError(s) => write!(f, "{}", s),
            HashToCurveError::MapToCurveError(s) => write!(f, "{}", s),
            HashToCurveError::HashToFieldError(s) => write!(f, "{}", s),
        }
    }
}

#[cfg(test)]
mod tests;
