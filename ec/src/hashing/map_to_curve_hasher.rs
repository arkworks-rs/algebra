use crate::{hashing::*, AffineRepr, CurveGroup};
use ark_ff::field_hashers::HashToField;
use ark_std::marker::PhantomData;

/// Trait for mapping a random field element to a random curve point.
pub trait MapToCurve<T: CurveGroup>: Sized {
    /// Constructs a new mapping.
    fn new() -> Result<Self, HashToCurveError>;

    /// Map an arbitary field element to a corresponding curve point.
    fn map_to_curve(&self, point: T::BaseField) -> Result<T::Affine, HashToCurveError>;
}

/// Helper struct that can be used to construct elements on the elliptic curve
/// from arbitrary messages, by first hashing the message onto a field element
/// and then mapping it to the elliptic curve defined over that field.
pub struct MapToCurveBasedHasher<T, H2F, M2C>
where
    T: CurveGroup,
    H2F: HashToField<T::BaseField>,
    M2C: MapToCurve<T>,
{
    field_hasher: H2F,
    curve_mapper: M2C,
    _params_t: PhantomData<T>,
}

impl<T, H2F, M2C> HashToCurve<T> for MapToCurveBasedHasher<T, H2F, M2C>
where
    T: CurveGroup,
    H2F: HashToField<T::BaseField>,
    M2C: MapToCurve<T>,
{
    fn new(domain: &[u8]) -> Result<Self, HashToCurveError> {
        let field_hasher = H2F::new(domain);
        let curve_mapper = M2C::new()?;
        let _params_t = PhantomData;
        Ok(MapToCurveBasedHasher {
            field_hasher,
            curve_mapper,
            _params_t,
        })
    }

    // Produce a hash of the message, using the hash to field and map to curve
    // traits. This uses the IETF hash to curve's specification for Random
    // oracle encoding (hash_to_curve) defined by combining these components.
    // See https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-09#section-3
    fn hash(&self, msg: &[u8]) -> Result<T::Affine, HashToCurveError> {
        // IETF spec of hash_to_curve, from hash_to_field and map_to_curve
        // sub-components
        // 1. u = hash_to_field(msg, 2)
        // 2. Q0 = map_to_curve(u[0])
        // 3. Q1 = map_to_curve(u[1])
        // 4. R = Q0 + Q1              # Point addition
        // 5. P = clear_cofactor(R)
        // 6. return P

        let rand_field_elems = self.field_hasher.hash_to_field(msg, 2);

        let rand_curve_elem_0 = self.curve_mapper.map_to_curve(rand_field_elems[0])?;
        let rand_curve_elem_1 = self.curve_mapper.map_to_curve(rand_field_elems[1])?;

        let rand_curve_elem = (rand_curve_elem_0 + rand_curve_elem_1).into();
        let rand_subgroup_elem = rand_curve_elem.clear_cofactor();

        Ok(rand_subgroup_elem)
    }
}
