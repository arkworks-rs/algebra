use crate::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_std::{marker::PhantomData, string::{ToString, String}, vec::Vec};
use core::fmt;
use digest::{Update, VariableOutput};

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

/// Trait for mapping a random field element to a random curve point.
pub trait MapToCurve<T: AffineCurve>: Sized {
    fn new_map_to_curve(domain: &[u8]) -> Result<Self, HashToCurveError>;
    /// Map random field point to a random curve point
    fn map_to_curve(&self, point: T::BaseField) -> Result<T, HashToCurveError>;
}

pub trait HashToField<F: Field>: Sized {
    fn new_hash_to_field(domain: &[u8]) -> Result<Self, HashToCurveError>;

    fn hash_to_field(&self, msg: &[u8], count: usize) -> Result<Vec<F>, HashToCurveError>;
}

fn hash_len_in_bytes<F: Field>(security_parameter: usize, count: usize) -> usize {
    // ceil(log(p))
    let base_field_size_in_bits = F::BasePrimeField::size_in_bits();
    // ceil(log(p)) + security_parameter
    let base_field_size_with_security_padding_in_bits = 
        base_field_size_in_bits + security_parameter;
    // ceil( (ceil(log(p)) + security_parameter) / 8)
    let bytes_per_base_field_elem = ((base_field_size_with_security_padding_in_bits + 7) / 8) as u64;
    let len_in_bytes = F::extension_degree() * (count as u64) * bytes_per_base_field_elem;
    len_in_bytes as usize
}

pub struct FieldHasher<H: VariableOutput + Update + Sized + Clone>
{
    // This hasher should already have the domain applied to it.
    hasher: H,
}

// Implement HashToField from F and a variable output hash
impl<F: Field, H: VariableOutput + Update + Sized + Clone> HashToField<F> for FieldHasher<H> {
    fn new_hash_to_field(domain: &[u8]) -> Result<Self, HashToCurveError>
    {
        // Hardcode security parameter
        let security_parameter = 128;
        // Hardcode count (TODO: Should we undo this?)
        let count = 2;
        let bytes_per_base_field_elem = hash_len_in_bytes::<F>(security_parameter, count);
        let hasher = H::new(bytes_per_base_field_elem);
        let mut unwrapped_hasher = match hasher {
            Ok(hasher) => hasher,
            Err(err) => return Err(HashToCurveError::DomainError(err.to_string())),
        };
        // TODO: Handle unwrapped_hasher.update(&domain) 
        // decide on what domain format do we want. (Pre-hash and prefix, or length prefix and then include it?)
        // I currently prefer pre-hashing it.
        // if domain.len() > 255 {

        // }
        // if domain.len() != 0 {
            
        // }
        Ok(FieldHasher{hasher: unwrapped_hasher})
    }

    fn hash_to_field(&self, msg: &[u8], count: usize) -> Result<Vec<F>, HashToCurveError> {
        Err(HashToCurveError::HashingError("unimplemented".to_string()))
    }
}

pub struct MapToCurveBasedHasher<T, H2F, M2C>
where
    T: AffineCurve,
    H2F: HashToField<T::BaseField>,
    M2C: MapToCurve<T>,
{
    field_hasher: H2F,
    curve_mapper: M2C,
    _params_t: PhantomData<T>
}

impl<T, H2F, M2C> HashToCurve<T> for MapToCurveBasedHasher<T, H2F, M2C>
where
    T: AffineCurve,
    H2F: HashToField<T::BaseField>,
    M2C: MapToCurve<T>,
{
    fn new(domain: &[u8]) -> Result<Self, HashToCurveError> {
        let field_hasher = H2F::new_hash_to_field(domain)?;
        let curve_mapper = M2C::new_map_to_curve(domain)?;
        let _params_t = PhantomData;
        Ok(MapToCurveBasedHasher {
            field_hasher,
            curve_mapper,
            _params_t,
        })
    }

    // Produce a hash of the message, using the hash to field and map to curve traits.
    // This uses the IETF hash to curve's specification for Random oracle encoding (hash_to_curve)
    // defined by combining these components.
    // See https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-09#section-3
    fn hash(&self, msg: &[u8]) -> Result<T, HashToCurveError> {
        // IETF spec of hash_to_curve, from hash_to_field and map_to_curve sub-components
        // 1. u = hash_to_field(msg, 2)
        // 2. Q0 = map_to_curve(u[0])
        // 3. Q1 = map_to_curve(u[1])
        // 4. R = Q0 + Q1              # Point addition
        // 5. P = clear_cofactor(R)
        // 6. return P

        let rand_field_elems = self.field_hasher.hash_to_field(msg, 2)?;

        let rand_curve_elem_0 = self.curve_mapper.map_to_curve(rand_field_elems[0])?;
        let rand_curve_elem_1 = self.curve_mapper.map_to_curve(rand_field_elems[1])?;

        let rand_curve_elem = rand_curve_elem_0 + rand_curve_elem_1;
        let rand_subgroup_elem = rand_curve_elem.mul_by_cofactor();

        Ok(rand_subgroup_elem)
    }
}
