//! # Hash-to-curve
//! 
//! Implements traits and map-to-curve operations for the 
//! [IRTF CFRG hash-to-curve draft](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16)

pub mod swu;
pub mod wb;


use ark_std::string::String;
use core::fmt;

pub use ark_ff::field_hashers::{
    self,AsDST,Expander,Zpad,
    digest::{self,FixedOutputReset,Update,XofReader}
};

use crate::{CurveGroup,AffineRepr};


/// Trait for mapping a random field element to a random curve point.
pub trait MapToCurve<C: CurveGroup>: Sized {
    /// Security parameters used by symetric components. 
    /// Almost always 128 bits, unsued if merely supporting WB.
    const SEC_PARAM: u16 = 128;

    /// Checks whether supplied parameters represent a valid map.
    fn check_parameters() -> Result<(), HashToCurveError>;

    /// Map an arbitary field element to a corresponding curve point.
    fn map_to_curve(point: C::BaseField) -> Result<C::Affine, HashToCurveError>;
}

/// Applies a map-to-curve to a hash-to-base-field fed by an
/// extendable output hash function (XoF), as in the 
/// [IRTF CFRG hash-to-curve draft](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16)
pub fn xof_map_to_curve<C,M,H>(xof: &mut H) -> Result<C, HashToCurveError> 
where C: CurveGroup, M: MapToCurve<C>, H: XofReader,
{
    let mut f = || match <M as MapToCurve<C>>::SEC_PARAM {
        128 => field_hashers::hash_to_field::<128u16,C::BaseField,H>(xof),
        256 => field_hashers::hash_to_field::<256u16,C::BaseField,H>(xof),
        _ => panic!("const-generics"),
    };
    let p0 = <M as MapToCurve<C>>::map_to_curve(f())?;
    let p1 = <M as MapToCurve<C>>::map_to_curve(f())?;

    // We've no projective clear_cofactor metho so normalize twice.
    Ok( (p0 + p1).into_affine().clear_cofactor().into_group() )
}

/// Applies the domain seperation tag (DST) to the hasher, and then
/// completes teh hash-to-curve, as in the 
/// [IRTF CFRG hash-to-curve draft](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16)
pub fn expand_to_curve<C,M>(exp: impl Expander, dst: impl AsDST) -> Result<C, HashToCurveError> 
where C: CurveGroup, M: MapToCurve<C>
{
    #[cfg(debug_assertions)]
    <M as MapToCurve<C>>::check_parameters()?;
    let mut xof = match <M as MapToCurve<C>>::SEC_PARAM {
        128 => exp.expand_for_field::<128u16,C::BaseField,2>(dst),
        256 => exp.expand_for_field::<256u16,C::BaseField,2>(dst),
        _ => panic!("const-generics"),
    };
    xof_map_to_curve::<C,M,_>(&mut xof)
}

/// Hash-to-curves need an extendable output hash function (XoF).
/// Initalizes sha2 flavors for the sha2 XoF hack from the
/// [IRTF CFRG hash-to-curve draft](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16)
/// 
/// All newer curves should prefer true XoFs like shake128 or similar
/// instead, which you initilize like `sha3::Shake128::default()`.
/// All higher security level curves must use shake256 or similar, not sha2.
pub fn zpad_expander<C,M,H>() -> Zpad<H>
where C: CurveGroup, M: MapToCurve<C>, H: FixedOutputReset+Default,
{
    match <M as MapToCurve<C>>::SEC_PARAM {
        128 => Zpad::<H>::new_for_field::<128u16,C::BaseField>(),
        256 => Zpad::<H>::new_for_field::<256u16,C::BaseField>(),
        _ => panic!("const-generics"),
    }
}

/// [IRTF CFRG hash-to-curve draft](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16)
/// based upon a map-to-curve and an extendable output hash function (XoF).
/// 
/// We expect isogenious curves to have incompatible hash-to-curves,
/// ala Bandersnarh in short Weierstrass or twisted Edwards forms. 
pub trait HashToCurve: CurveGroup {
    type Map: MapToCurve<Self>;
    type Expand: Expander+Update;

    /// Initalize the standard hasher for this hash-to-curve.
    fn expander() -> Self::Expand;

    fn finalize_to_curve(exp: impl Expander, dst: impl AsDST) -> Result<Self, HashToCurveError> {
        expand_to_curve::<Self,Self::Map>(exp,dst)
    }

    fn hash_to_curve(dst: impl AsDST, msg: &[u8]) -> Result<Self, HashToCurveError> {
        let mut exp = Self::expander();
        exp.update(msg);
        Self::finalize_to_curve(exp, dst)
    }
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
