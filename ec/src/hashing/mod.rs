use crate::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_std::{marker::PhantomData, string::{String, ToString}};
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
pub trait MapToCurve<T: AffineCurve> : Sized {
    fn new_map_to_curve(domain: &[u8]) -> Result<Self, HashToCurveError>;
    /// Map random field point to a random curve point
    fn map_to_curve(&self, point: T::BaseField) -> Result<T, HashToCurveError>;
}

pub trait HashToField<F: Field, H: VariableOutput + Update> : Sized {
    fn new_hash_to_field(domain: &[u8]) -> Result<Self, HashToCurveError>;

    fn hash_to_field(&self, msg: &[u8]) -> Result<F, HashToCurveError>;
}

pub struct MapToCurveBasedHasher<T, CRH, H2F, M2C> where 
    T: AffineCurve, 
    CRH: VariableOutput + Update,
    H2F: HashToField<T::BaseField, CRH>,
    M2C: MapToCurve<T>, {
    field_hasher: H2F,
    curve_mapper: M2C,
    _params_t: PhantomData<T>,
    _params_crh: PhantomData<CRH>,
}

impl<T, CRH, H2F, M2C> HashToCurve<T> for MapToCurveBasedHasher<T, CRH, H2F, M2C> where 
    T: AffineCurve, 
    CRH: VariableOutput + Update,
    H2F: HashToField<T::BaseField, CRH>,
    M2C: MapToCurve<T> 
    {
    fn new(domain: &[u8]) -> Result<Self, HashToCurveError> {
        let field_hasher = H2F::new_hash_to_field(domain)?;
        let curve_mapper = M2C::new_map_to_curve(domain)?;
        let _params_t = PhantomData;
        let _params_crh = PhantomData;
        Ok(MapToCurveBasedHasher{field_hasher, curve_mapper, _params_t, _params_crh})
    }

        // Produce a hash of the message, using the hash to field and map to curve traits.
    // This uses the IETF hash to curve's specification for Random oracle encoding (hash_to_curve) 
    // defined by combining these components.
    // See https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-09#section-3
    fn hash(
        &self,
        msg: &[u8],
    ) -> Result<T, HashToCurveError>
    {
        // IETF spec of hash_to_curve, from hash_to_field and map_to_curve sub-components
        // 1. u = hash_to_field(msg, 2)
        // 2. Q0 = map_to_curve(u[0])
        // 3. Q1 = map_to_curve(u[1])
        // 4. R = Q0 + Q1              # Point addition
        // 5. P = clear_cofactor(R)
        // 6. return P
        let mut msg_0 = vec![0u8];
        let mut msg_1 = vec![1u8];
        msg_0.extend_from_slice(msg);
        msg_1.extend_from_slice(msg);

        let rand_field_elem_0 = self.field_hasher.hash_to_field(&msg_0)?;
        let rand_field_elem_1 = self.field_hasher.hash_to_field(&msg_1)?;

        let rand_curve_elem_0 = self.curve_mapper.map_to_curve(rand_field_elem_0)?;
        let rand_curve_elem_1 = self.curve_mapper.map_to_curve(rand_field_elem_1)?;

        let rand_curve_elem = rand_curve_elem_0 + rand_curve_elem_1;
        let rand_subgroup_elem = rand_curve_elem.mul_by_cofactor();

        Ok(rand_subgroup_elem)
    }
}