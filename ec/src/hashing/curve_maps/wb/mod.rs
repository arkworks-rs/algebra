use core::marker::PhantomData;

use crate::{models::SWModelParameters, ModelParameters};
use ark_ff::batch_inversion;
use ark_poly::{univariate::DensePolynomial, Polynomial, UVPolynomial};

use crate::{
    hashing::{map_to_curve_hasher::MapToCurve, HashToCurveError},
    models::short_weierstrass_jacobian::GroupAffine,
    AffineCurve,
};

use super::swu::{SWUMap, SWUParams};
type BaseField<MP> = <MP as ModelParameters>::BaseField;

/// Trait defining the necessary parameters for the WB hash-to-curve method
/// for the curves of Weierstrass form of:
/// of y^2 = x^3 + a*x + b where b != 0 but `a` can be zero like BLS-381 curve.
/// From [\[WB2019\]]
///
/// - [\[WB2019\]] <http://dx.doi.org/10.46586/tches.v2019.i4.154-179>
pub trait WBParams: SWModelParameters + Sized {
    // The isogenous curve should be defined over the same base field but it can have
    // different scalar field type IsogenousCurveScalarField :
    type IsogenousCurve: SWUParams<BaseField = BaseField<Self>>;

    const PHI_X_NOM: &'static [BaseField<Self>];
    const PHI_X_DEN: &'static [BaseField<Self>];

    const PHI_Y_NOM: &'static [BaseField<Self>];
    const PHI_Y_DEN: &'static [BaseField<Self>];

    fn isogeny_map(
        domain_point: GroupAffine<Self::IsogenousCurve>,
    ) -> Result<GroupAffine<Self>, HashToCurveError> {
        let x_num = DensePolynomial::from_coefficients_slice(&Self::PHI_X_NOM[..]);
        let x_den = DensePolynomial::from_coefficients_slice(&Self::PHI_X_DEN[..]);

        let y_num = DensePolynomial::from_coefficients_slice(&Self::PHI_Y_NOM[..]);
        let y_den = DensePolynomial::from_coefficients_slice(&Self::PHI_Y_DEN[..]);

        let mut v: [BaseField<Self>; 2] = [
            x_den.evaluate(&domain_point.x),
            y_den.evaluate(&domain_point.x),
        ];
        batch_inversion(&mut v);
        let img_x = x_num.evaluate(&domain_point.x) * v[0];
        let img_y = (y_num.evaluate(&domain_point.x) * domain_point.y) * v[1];

        Ok(GroupAffine::new(img_x, img_y, false))
    }
}

pub struct WBMap<P: WBParams> {
    swu_field_curve_hasher: SWUMap<P::IsogenousCurve>,
    curve_params: PhantomData<fn() -> P>,
}

impl<P: WBParams> MapToCurve<GroupAffine<P>> for WBMap<P> {
    /// Constructs a new map if `P` represents a valid map.
    fn new_map_to_curve() -> Result<Self, HashToCurveError> {
        // Verifying that the isogeny maps the generator of the SWU curve into us
        let isogenous_curve_generator = GroupAffine::<P::IsogenousCurve>::new(
            P::IsogenousCurve::AFFINE_GENERATOR_COEFFS.0,
            P::IsogenousCurve::AFFINE_GENERATOR_COEFFS.1,
            false,
        );

        match P::isogeny_map(isogenous_curve_generator) {
            Ok(point_on_curve) => {
                if !point_on_curve.is_on_curve() {
                    return Err(HashToCurveError::MapToCurveError(format!("the isogeny maps the generator of its domain: {} into {} which does not belong to its codomain.",isogenous_curve_generator, point_on_curve)));
                }
            },
            Err(e) => return Err(e),
        }

        Ok(WBMap {
            swu_field_curve_hasher: SWUMap::<P::IsogenousCurve>::new_map_to_curve().unwrap(),
            curve_params: PhantomData,
        })
    }

    /// Map random field point to a random curve point
    /// inspired from
    /// <https://github.com/zcash/pasta_curves/blob/main/src/hashtocurve.rs>
    fn map_to_curve(
        &self,
        element: <GroupAffine<P> as AffineCurve>::BaseField,
    ) -> Result<GroupAffine<P>, HashToCurveError> {
        // first we need to map the field point to the isogenous curve
        let point_on_isogenious_curve = self.swu_field_curve_hasher.map_to_curve(element).unwrap();
        P::isogeny_map(point_on_isogenious_curve)
    }
}
