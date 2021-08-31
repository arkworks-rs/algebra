use core::marker::PhantomData;

use ark_ff::{Field, PrimeField, SquareRootField};
use ark_ff::vec::Vec;
use crate::models::SWModelParameters;

use crate::hashing::map_to_curve_hasher::MapToCurve;
use crate::hashing::HashToCurveError;
use crate::{AffineCurve};
use crate::models::short_weierstrass_jacobian::GroupAffine;

/// Implementation for the SWU hash to curve for the curves of Weierstrass form of y^2 = x^3 + a*x + b where ab != 0. From [WB2019]
///
/// - [WB19] Wahby, R. S., & Boneh, D. (2019). Fast and simple constant-time
///   hashing to the bls12-381 elliptic curve. IACR Transactions on
///   Cryptographic Hardware and Embedded Systems, nil(nil), 154–179.
///   http://dx.doi.org/10.46586/tches.v2019.i4.154-179
///
///
pub trait SWUParams : SWModelParameters {
    // a non-zero element of F meeting the below criteria.
    // Let g(x) be the value of y^2, e.g. g(x) = x^3 + Ax + B
    // 1.  g(Z) != 0 in F.
    // 2.  -(3 * Z^2 + 4 * A) / (4 * g(Z)) != 0 in F.
    // 3.  -(3 * Z^2 + 4 * A) / (4 * g(Z)) is square in F.
    // 4.  At least one of g(Z) and g(-Z / 2) is square in F.
    const Z : Self::BaseField;
    // we need an element of the base field which is not a square root see [1] Sect. 4.
    // it is also convenient to have $g(b/xi * a)$ to be square. In general we use a xi with
    // low absolute value coefficients when they are represented as element of ZZ.
    const XI : Self::BaseField;
    const ZETA: Self::BaseField; //arbitatry root of unity
    const XI_ON_ZETA_SQRT: Self::BaseField; //square root of THETA
    
}

pub struct SWU_hasher<P: SWUParams> {
    pub domain: Vec<u8>,
    curve_params: PhantomData<fn() -> P>,
}

impl <P: SWUParams> MapToCurve<GroupAffine<P>> for SWU_hasher<P>{

    ///This is to verify if the provided SWUparams makes sense, doesn't do much for now
    fn new_map_to_curve(domain: &[u8]) -> Result<Self, HashToCurveError>
    {
        Ok(SWU_hasher {
            domain: domain.to_vec(),
            curve_params: PhantomData,
        })
    }
    
    /// Map random field point to a random curve point
    /// inspired from
    /// https://github.com/zcash/pasta_curves/blob/main/src/hashtocurve.rs
    fn map_to_curve(&self, point: <GroupAffine<P> as AffineCurve>::BaseField) -> Result<GroupAffine<P>, HashToCurveError>  {
    // 1. tv1 = inv0(Z^2 * u^4 + Z * u^2)
    // 2. x1 = (-B / A) * (1 + tv1)
    // 3. If tv1 == 0, set x1 = B / (Z * A)
    // 4. gx1 = x1^3 + A * x1 + B
    //
    // We use the "Avoiding inversions" optimization in [WB2019, section 4.2]
    // (not to be confused with section 4.3):
    //
    //   here       [WB2019]
    //   -------    ---------------------------------
    //   Z          ξ
    //   u          t
    //   Z * u^2    ξ * t^2 (called u, confusingly)
    //   x1         X_0(t)
    //   x2         X_1(t)
    //   gx1        g(X_0(t))
    //   gx2        g(X_1(t))
    //
    // Using the "here" names:
    //    x1 = num_x1/div      = [B*(Z^2 * u^4 + Z * u^2 + 1)] / [-A*(Z^2 * u^4 + Z * u^2]
    //   gx1 = num_gx1/div_gx1 = [num_x1^3 + A * num_x1 * div^2 + B * div^3] / div^3

    let a = P::COEFF_A;
    let b = P::COEFF_B;
    let xi_t2 = P::XI * point.square();
    let ta = xi_t2.square() + xi_t2;
    let num_x1 = b * (ta + P::BaseField::one());
    let div = a * if (ta.is_zero()) { -ta} else { P::XI };
    let num2_x1 = num_x1.square();
    let div2 = div.square();
    let div3 = div2 * div;
    let num_gx1 = (num2_x1 + a * div2) * num_x1 + b * div3;

    // 5. x2 = Z * u^2 * x1
    let num_x2 = xi_t2 * num_x1; // same div

    // 6. gx2 = x2^3 + A * x2 + B  [optimized out; see below]
    // 7. If is_square(gx1), set x = x1 and y = sqrt(gx1)
    // 8. Else set x = x2 and y = sqrt(gx2)
    let mut gx1_square = false;
    let gx1 = num_gx1;
    let zeta_gx1 = P::ZETA;


        let y1 = if (div3.is_zero) {
            0
        }
        else 
        {
            gx1 = (num_gx1 / div3);
            zeta_gx1 = P::ZETA*gx1;
            if gx1.is_square() {
                gx1_square = false;
                gx1.sqrt()

            } else {
                gx1_square = true;
                zeta_gx1.sqrt()

            }
        };
            
    // This magic also comes from a generalization of [WB2019, section 4.2].
    //
    // The Sarkar square root algorithm with input s gives us a square root of
    // h * s for free when s is not square, where h is a fixed nonsquare.
    // In our implementation, h = ROOT_OF_UNITY.
    // We know that Z / h is a square since both Z and h are
    // nonsquares. Precompute theta as a square root of Z / ROOT_OF_UNITY.
    //
    // We have gx2 = g(Z * u^2 * x1) = Z^3 * u^6 * gx1
    //                               = (Z * u^3)^2 * (Z/h * h * gx1)
    //                               = (Z * theta * u^3)^2 * (h * gx1)
    //
    // When gx1 is not square, y1 is a square root of h * gx1, and so Z * theta * u^3 * y1
    // is a square root of gx2. Note that we don't actually need to compute gx2.

    let y2 = P::XI_ON_ZETA_SQRT * xi_t2 * point * y1;
        let num_x = if gx1_square { num2_x1} else {num_x1};

    //it seems that we only need to return x
    num_x * div
    // let y = if {gx1_square} {y2} else {y1};

    //     // 9. If sgn0(u) != sgn0(y), set y = -y
    // let y = if y % 2 {-y} or {y};
    // I::new_jacobian(num_x * div, y * div3, div).unwrap()

    }
}
