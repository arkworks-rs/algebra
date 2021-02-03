use crate::hashing::*;
use crate::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_std::{
    marker::PhantomData,
    string::{String, ToString},
    vec::Vec,
};
use core::fmt;
use digest::{Update, VariableOutput};

/// Trait for mapping a random field element to a random curve point.
pub trait MapToCurve<T: AffineCurve>: Sized {
    fn new_map_to_curve(domain: &[u8]) -> Result<Self, HashToCurveError>;
    /// Map random field point to a random curve point
    fn map_to_curve(&self, point: T::BaseField) -> Result<T, HashToCurveError>;
}

// Trait for hashing messages to field elements
pub trait HashToField<F: Field>: Sized {
    fn new_hash_to_field(domain: &[u8], count: usize) -> Result<Self, HashToCurveError>;

    fn hash_to_field(&self, msg: &[u8]) -> Result<Vec<F>, HashToCurveError>;
}

pub struct MapToCurveBasedHasher<T, H2F, M2C>
where
    T: AffineCurve,
    H2F: HashToField<T::BaseField>,
    M2C: MapToCurve<T>,
{
    field_hasher: H2F,
    curve_mapper: M2C,
    _params_t: PhantomData<T>,
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
