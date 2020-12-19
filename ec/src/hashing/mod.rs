use crate::AffineCurve;
use ark_std::string::String;
use core::fmt;
use digest::{Update, VariableOutput};

/// Trait for hashing arbitrary data to a group element on an elliptic curve
pub trait HashToCurve<T: AffineCurve> : Sized {
    /// Create a new hash to curve instance, with a given domain.
    fn new(domain: &[u8]) -> Result<Self, HashToCurveError>;

    /// Produce a hash of the message, which also depends on the domain.
    /// The output of the hash is a curve point in the prime order subgroup
    /// of the given elliptic curve.
    fn hash(
        &self,
        salt: &[u8],
        message: &[u8],
    ) -> Result<T, HashToCurveError>;
}

/// This is an error that could occur during circuit synthesis contexts,
/// such as CRS generation, proving or verification.
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

/// Trait for mapping a random field element to a random curve point.
pub trait MapToCurve<T: AffineCurve> {
    /// Map random field point to a random curve point
    fn map_to_curve(point: T::BaseField) -> Result<T, HashToCurveError>;
}

pub trait HashToField<F: PrimeField, H: VariableOutput + Clone + Update> {
    fn new(domain: &[u8]) -> Result<Self, HashToCurveError>;

    fn hash_to_field(&self, msg: &[u8]) -> Result<F, HashToFieldError>;
}

impl<F: PrimeField, T: AffineCurve, H: VariableOutput + Clone + Update, H2F: HashToField<F, H>, M: MapToCurve> 