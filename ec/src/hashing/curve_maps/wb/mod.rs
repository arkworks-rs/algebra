use core::marker::PhantomData;

use ark_ff::{Zero, One, Field, PrimeField, SquareRootField};
use ark_ff::vec::Vec;
use crate::models::SWModelParameters;

use crate::hashing::map_to_curve_hasher::MapToCurve;
use crate::hashing::HashToCurveError;
use crate::{AffineCurve};
use crate::models::short_weierstrass_jacobian::GroupAffine;

/// Implementation for the WB hash to curve for the curves of Weierstrass form of y^2 = x^3 + a*x + b where b != 0 but a can be zero like BLS-381 curve. From [WB2019]
///
/// - [WB19] Wahby, R. S., & Boneh, D. (2019). Fast and simple constant-time
///   hashing to the bls12-381 elliptic curve. IACR Transactions on
///   Cryptographic Hardware and Embedded Systems, nil(nil), 154–179.
///   http://dx.doi.org/10.46586/tches.v2019.i4.154-179
///
///
pub trait WBParams : SWModelParameters {

    //TODO: We need to define both the isogeny map and the isogenous curve
    const ISOGENOUS_CURVE: SWUParam;

    const isogeny_map: fn(domain_point: GroupAffine<ISOGENOUS_CURVE>) -> GroupAffine<Self>;
    
}

pub struct WBMap<P: WBParams> {
    pub domain: Vec<u8>,
    curve_params: PhantomData<fn() -> P>,
}

impl <P: WBParams> MapToCurve<GroupAffine<P>> for WBMap<P>{

    ///This is to verify if the provided WBparams makes sense, doesn't do much for now
    fn new_map_to_curve(domain: &[u8]) -> Result<Self, HashToCurveError>
    {
        Ok(WBMap {
            domain: domain.to_vec(),
            curve_params: PhantomData,
        })
    }
    
    /// Map random field point to a random curve point
    /// inspired from
    /// https://github.com/zcash/pasta_curves/blob/main/src/hashtocurve.rs
    fn map_to_curve(&self, point: <GroupAffine<P> as AffineCurve>::BaseField) -> Result<GroupAffine<P>, HashToCurveError>  {
	//TODO
    }
}
