use crate::models::short_weierstrass::SWCurveConfig;
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_std::string::ToString;
use core::marker::PhantomData;

use crate::{
    hashing::{map_to_curve_hasher::MapToCurve, HashToCurveError},
    models::short_weierstrass::{Affine, Projective},
};

/// Trait defining the necessary parameters for the SWU hash-to-curve method
/// for the curves of Weierstrass form of:
/// y^2 = x^3 + a*x + b where ab != 0. From [\[WB2019\]]
///
/// - [\[WB2019\]] <https://eprint.iacr.org/2019/403>
pub trait SWUConfig: SWCurveConfig {
    /// An element of the base field that is not a square root see \[WB2019, Section 4\].
    /// It is also convenient to have $g(b/ZETA * a)$ to be square. In general
    /// we use a `ZETA` with low absolute value coefficients when they are
    /// represented as integers.
    const ZETA: Self::BaseField;
}

/// Represents the SWU hash-to-curve map defined by `P`.
pub struct SWUMap<P: SWUConfig>(PhantomData<fn() -> P>);

/// Trait defining a parity method on the Field elements based on [\[1\]] Section 4.1
///
/// - [\[1\]] <https://datatracker.ietf.org/doc/draft-irtf-cfrg-hash-to-curve/>
pub fn parity<F: Field>(element: &F) -> bool {
    element
        .to_base_prime_field_elements()
        .find(|&x| !x.is_zero())
        .map_or(false, |x| x.into_bigint().is_odd())
}

impl<P: SWUConfig> MapToCurve<Projective<P>> for SWUMap<P> {
    /// Constructs a new map if `P` represents a valid map.
    fn new() -> Result<Self, HashToCurveError> {
        // Verifying that ZETA is a non-square
        if P::ZETA.legendre().is_qr() {
            return Err(HashToCurveError::MapToCurveError(
                "ZETA should be a quadratic non-residue for the SWU map".to_string(),
            ));
        }

        // Verifying the prerequisite for applicability  of SWU map
        if P::COEFF_A.is_zero() || P::COEFF_B.is_zero() {
            return Err(HashToCurveError::MapToCurveError("Simplified SWU requires a * b != 0 in the short Weierstrass form of y^2 = x^3 + a*x + b ".to_string()));
        }

        Ok(SWUMap(PhantomData))
    }

    /// Map an arbitrary base field element to a curve point.
    /// Based on
    /// <https://github.com/zcash/pasta_curves/blob/main/src/hashtocurve.rs>.
    fn map_to_curve(&self, point: P::BaseField) -> Result<Affine<P>, HashToCurveError> {
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

        let zeta_u2 = P::ZETA * point.square();
        let ta = zeta_u2.square() + zeta_u2;
        let num_x1 = b * (ta + <P::BaseField as One>::one());
        let div = a * if ta.is_zero() { P::ZETA } else { -ta };

        let num2_x1 = num_x1.square();
        let div2 = div.square();
        let div3 = div2 * div;
        let num_gx1 = (num2_x1 + a * div2) * num_x1 + b * div3;

        // 5. x2 = Z * u^2 * x1
        let num_x2 = zeta_u2 * num_x1; // same div

        // 6. gx2 = x2^3 + A * x2 + B  [optimized out; see below]
        // 7. If is_square(gx1), set x = x1 and y = sqrt(gx1)
        // 8. Else set x = x2 and y = sqrt(gx2)
        let gx1_square;
        let gx1;

        assert!(
            !div3.is_zero(),
            "we have checked that neither a or ZETA are zero. Q.E.D."
        );
        let y1: P::BaseField = {
            gx1 = num_gx1 / div3;
            if gx1.legendre().is_qr() {
                gx1_square = true;
                gx1.sqrt()
                    .expect("We have checked that gx1 is a quadratic residue. Q.E.D")
            } else {
                let zeta_gx1 = P::ZETA * gx1;
                gx1_square = false;
                zeta_gx1.sqrt().expect(
                    "ZETA * gx1 is a quadratic residue because legard is multiplicative. Q.E.D",
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

        let y2 = zeta_u2 * point * y1;
        let num_x = if gx1_square { num_x1 } else { num_x2 };
        let y = if gx1_square { y1 } else { y2 };

        let x_affine = num_x / div;
        let y_affine = if parity(&y) != parity(&point) { -y } else { y };
        let point_on_curve = Affine::<P>::new_unchecked(x_affine, y_affine);
        assert!(
            point_on_curve.is_on_curve(),
            "swu mapped to a point off the curve"
        );
        Ok(point_on_curve)
    }
}

#[cfg(test)]
mod test {
    use crate::{
        hashing::{map_to_curve_hasher::MapToCurveBasedHasher, HashToCurve},
        CurveConfig,
    };
    use ark_ff::field_hashers::DefaultFieldHasher;
    use ark_std::vec::Vec;

    use super::*;
    use ark_ff::{fields::Fp64, MontBackend, MontFp};
    use hashbrown::HashMap;
    use sha2::Sha256;

    #[derive(ark_ff::MontConfig)]
    #[modulus = "127"]
    #[generator = "6"]
    pub struct F127Config;
    pub type F127 = Fp64<MontBackend<F127Config, 1>>;

    const F127_ONE: F127 = MontFp!("1");

    struct TestSWUMapToCurveConfig;

    impl CurveConfig for TestSWUMapToCurveConfig {
        const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
        const COFACTOR_INV: F127 = F127_ONE;

        type BaseField = F127;
        type ScalarField = F127;
    }

    /// just because not defining another field
    ///
    /// from itertools import product
    /// p = 127
    /// FF = GF(p)
    /// for a,b in product(range(0,p), range(0,p)):
    ///     try:
    ///         E = EllipticCurve([FF(a),FF(b)])
    ///         if E.order() == p:
    ///             print(E)
    ///     except:
    ///         pass
    ///
    /// y^2 = x^3 + x + 63
    impl SWCurveConfig for TestSWUMapToCurveConfig {
        /// COEFF_A = 1
        const COEFF_A: F127 = F127_ONE;

        /// COEFF_B = 63
        const COEFF_B: F127 = MontFp!("63");

        /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
        const GENERATOR: Affine<Self> = Affine::new_unchecked(MontFp!("62"), MontFp!("70"));
    }

    impl SWUConfig for TestSWUMapToCurveConfig {
        const ZETA: F127 = MontFp!("-1");
    }

    /// test that MontFp make a none zero element out of 1
    #[test]
    fn test_field_element_construction() {
        let a1 = F127::from(1);
        let a2 = F127::from(2);
        let a3 = F127::from(125);

        assert!(F127::from(0) == a2 + a3);
        assert!(F127::from(0) == a2 * a1 + a3);
    }

    #[test]
    fn test_field_division() {
        let num = F127::from(0x3d);
        let den = F127::from(0x7b);
        let num_on_den = F127::from(0x50);

        assert!(num / den == num_on_den);
    }

    /// The point of the test is to get a simple SWU compatible curve and make
    /// simple hash
    #[test]
    fn hash_arbitary_string_to_curve_swu() {
        let test_swu_to_curve_hasher = MapToCurveBasedHasher::<
            Projective<TestSWUMapToCurveConfig>,
            DefaultFieldHasher<Sha256, 128>,
            SWUMap<TestSWUMapToCurveConfig>,
        >::new(&[1])
        .unwrap();

        let hash_result = test_swu_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

        assert!(
            hash_result.is_on_curve(),
            "hash results into a point off the curve"
        );
    }

    /// Use a simple SWU compatible curve and map the whole field to it. We observe
    /// the map behaviour. Specifically, the map should be non-constant, all
    /// elements should be mapped to curve successfully. everything can be mapped
    #[test]
    fn map_field_to_curve_swu() {
        let test_map_to_curve = SWUMap::<TestSWUMapToCurveConfig>::new().unwrap();

        let mut map_range: Vec<Affine<TestSWUMapToCurveConfig>> = vec![];
        for current_field_element in 0..127 {
            map_range.push(
                test_map_to_curve
                    .map_to_curve(F127::from(current_field_element as u64))
                    .unwrap(),
            );
        }

        let mut counts = HashMap::new();

        let mode = map_range
            .iter()
            .copied()
            .max_by_key(|&n| {
                let count = counts.entry(n).or_insert(0);
                *count += 1;
                *count
            })
            .unwrap();

        assert!(
            *counts.get(&mode).unwrap() != 127,
            "a constant hash function is not good."
        );
    }
}
