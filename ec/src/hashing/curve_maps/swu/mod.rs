use crate::models::SWModelParameters;
use ark_ff::{BigInteger, Field, One, PrimeField, SquareRootField, Zero};
use ark_std::string::ToString;
use core::marker::PhantomData;

use crate::{
    hashing::{map_to_curve_hasher::MapToCurve, HashToCurveError},
    models::short_weierstrass_jacobian::GroupAffine,
};

/// Trait defining the necessary parameters for the SWU hash-to-curve method
/// for the curves of Weierstrass form of:
/// y^2 = x^3 + a*x + b where ab != 0. From [\[WB2019\]]
///
/// - [\[WB2019\]] <https://eprint.iacr.org/2019/403>
pub trait SWUParams: SWModelParameters {
    /// An element of the base field that is not a square root see \[WB2019, Section 4\].
    /// It is also convenient to have $g(b/xi * a)$ to be square. In general
    /// we use a `XI` with low absolute value coefficients when they are
    /// represented as integers.
    const XI: Self::BaseField;
    /// An arbitrary nonsquare conviniently chosen to be a primitve element of the base field
    const ZETA: Self::BaseField;
    /// Square root of `THETA = Self::XI/Self::ZETA`.
    const XI_ON_ZETA_SQRT: Self::BaseField;
}

/// Represents the SWU hash-to-curve map defined by `P`.
pub struct SWUMap<P: SWUParams> {
    curve_params: PhantomData<fn() -> P>,
}

/// Trait defining a parity method on the Field elements based on [\[1\]] Section 4.1
///
/// - [\[1\]] <https://datatracker.ietf.org/doc/draft-irtf-cfrg-hash-to-curve/>
trait ElementParity<F: Field> {
    fn parity(element: &F) -> bool {
        element
            .to_base_prime_field_elements()
            .find(|&x| !x.is_zero())
            .map_or(false, |x| x.into_repr().is_odd())
    }
}

impl<P: SWUParams> ElementParity<P::BaseField> for SWUMap<P> {}

impl<P: SWUParams> MapToCurve<GroupAffine<P>> for SWUMap<P> {
    /// Constructs a new map if `P` represents a valid map.
    fn new_map_to_curve() -> Result<Self, HashToCurveError> {
        // Verifying that both XI and ZETA are non-squares
        if P::XI.legendre().is_qr() || P::ZETA.legendre().is_qr() {
            return Err(HashToCurveError::MapToCurveError(
                "both xi and zeta should be quadratic non-residues for the SWU map".to_string(),
            ));
        }

        // Verifying precomupted values
        let xi_on_zeta = P::XI / P::ZETA;
        match xi_on_zeta.sqrt() {
            Some(xi_on_zeta_sqrt) => {
                if xi_on_zeta_sqrt != P::XI_ON_ZETA_SQRT && xi_on_zeta_sqrt != -P::XI_ON_ZETA_SQRT {
                    return Err(HashToCurveError::MapToCurveError(
                        "precomputed P::XI_ON_ZETA_SQRT is not what it is supposed to be"
                            .to_string(),
                    ));
                }
            }
            None => {
                panic!(
                    "`xi_on_zeta` was expected to have a sqrt, since the numerator and denominator are non-residues and Legendre symbol is multiplicative. Q.E.D"
                );
            }
        }

        // Verifying the prerequisite for applicability  of SWU map
        if P::COEFF_A.is_zero() || P::COEFF_B.is_zero() {
            return Err(HashToCurveError::MapToCurveError("Simplified SWU requires a * b != 0 in the short Weierstrass form of y^2 = x^3 + a*x + b ".to_string()));
        }

        Ok(SWUMap {
            curve_params: PhantomData,
        })
    }

    /// Map an arbitrary base field element to a curve point.
    /// Based on
    /// <https://github.com/zcash/pasta_curves/blob/main/src/hashtocurve.rs>.
    fn map_to_curve(&self, point: P::BaseField) -> Result<GroupAffine<P>, HashToCurveError> {
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
        let num_x1 = b * (ta + <P::BaseField as One>::one());
        let div = a * if ta.is_zero() { P::XI } else { -ta };
        let num2_x1 = num_x1.square();
        let div2 = div.square();
        let div3 = div2 * div;
        let num_gx1 = (num2_x1 + a * div2) * num_x1 + b * div3;

        // 5. x2 = Z * u^2 * x1
        let num_x2 = xi_t2 * num_x1; // same div

        // 6. gx2 = x2^3 + A * x2 + B  [optimized out; see below]
        // 7. If is_square(gx1), set x = x1 and y = sqrt(gx1)
        // 8. Else set x = x2 and y = sqrt(gx2)
        let gx1_square;
        let gx1;
        let zeta_gx1;

        assert!(
            !div3.is_zero(),
            "we have checked that neither a or xi are zero. Q.E.D."
        );
        let y1: P::BaseField = {
            gx1 = num_gx1 / div3;
            zeta_gx1 = P::ZETA * gx1;
            if gx1.legendre().is_qr() {
                gx1_square = true;
                gx1.sqrt()
                    .expect("We have checked that gx1 is a quadratic residue. Q.E.D")
            } else {
                gx1_square = false;
                zeta_gx1.sqrt().expect(
                    "zeta * gx1 is a quadratic residue because legard is multiplicative. Q.E.D",
                )
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
        // When gx1 is not square, y1 is a square root of h * gx1, and so Z * theta *
        // u^3 * y1 is a square root of gx2. Note that we don't actually need to
        // compute gx2.

        let y2 = P::XI_ON_ZETA_SQRT * xi_t2 * point * y1;
        let num_x = if gx1_square { num_x1 } else { num_x2 };
        let y = if gx1_square { y1 } else { y2 };

        let x_affine = num_x / div;
        let y_affine = if Self::parity(&y) { -y } else { y };
        let point_on_curve = GroupAffine::<P>::new(x_affine, y_affine, false);
        assert!(
            point_on_curve.is_on_curve(),
            "swu mapped to a point off the curve"
        );
        Ok(point_on_curve)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_test_curves::bls12_381::{Fq, Fq2, Fq6};

    impl ElementParity<Fq> for Fq {}
    impl ElementParity<Fq2> for Fq2 {}
    impl ElementParity<Fq6> for Fq6 {}

    #[test]
    fn test_parity_of_prime_field_elements() {
        let a1 = Fq::from(0);
        let a2 = Fq::from(1);
        let a3 = Fq::from(10);
        assert_eq!(Fq::parity(&a1), false);
        assert_eq!(Fq::parity(&a2), true);
        assert_eq!(Fq::parity(&a3), false);
    }

    #[test]
    fn test_parity_of_quadratic_extension_elements() {
        let element_test1 = Fq2::new(Fq::from(0), Fq::from(1));
        let element_test2 = Fq2::new(Fq::from(1), Fq::from(0));
        let element_test3 = Fq2::new(Fq::from(10), Fq::from(5));
        let element_test4 = Fq2::new(Fq::from(5), Fq::from(10));
        assert_eq!(Fq2::parity(&element_test1), true, "parity is the oddness of first non-zero coefficient of element represented over the prime field" );
        assert_eq!(Fq2::parity(&element_test2), true);
        assert_eq!(Fq2::parity(&element_test3), false);
        assert_eq!(Fq2::parity(&element_test4), true);
    }

    #[test]
    fn test_parity_of_cubic_extension_elements() {
        let a1 = Fq2::new(Fq::from(0), Fq::from(0));
        let a2 = Fq2::new(Fq::from(0), Fq::from(1));
        let a3 = Fq2::new(Fq::from(1), Fq::from(0));
        let a4 = Fq2::new(Fq::from(1), Fq::from(1));
        let a5 = Fq2::new(Fq::from(0), Fq::from(2));

        let element_test1 = Fq6::new(a1, a2, a3);
        let element_test2 = Fq6::new(a2, a3, a4);
        let element_test3 = Fq6::new(a3, a4, a1);
        let element_test4 = Fq6::new(a4, a1, a2);
        let element_test5 = Fq6::new(a1, a5, a2);

        assert_eq!(Fq6::parity(&element_test1), true, "parity is the oddness of first non-zero coefficient of element represented over the prime field");
        assert_eq!(Fq6::parity(&element_test2), true, "parity is the oddness of first non-zero coefficient of element represented over the prime field");
        assert_eq!(Fq6::parity(&element_test3), true);
        assert_eq!(Fq6::parity(&element_test4), true);
        assert_eq!(Fq6::parity(&element_test5), false);
    }
}
