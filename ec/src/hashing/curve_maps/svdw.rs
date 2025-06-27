use crate::models::short_weierstrass::SWCurveConfig;
use ark_ff::{Field, One, Zero};
use core::marker::PhantomData;

use crate::{
    hashing::{curve_maps::parity, map_to_curve_hasher::MapToCurve, HashToCurveError},
    models::short_weierstrass::{Affine, Projective},
};

/// Trait defining the necessary parameters for the SVDW hash-to-curve method
/// for the curves of Weierstrass form of:
/// y^2 = x^3 + a*x + b. From IETF draft draft-irtf-cfrg-hash-to-curve-16
/// <https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16#section-6.6.1>
pub trait SVDWConfig: SWCurveConfig {
    /// An element Z of the base field F such that Z is non-zero,
    /// Z is not a square in F, and the curve E' defined by
    /// y^2 = x^3 + A' * x + B' (where A' = A * Z^2, B' = B * Z^3)
    /// has a point of order L (the order of the subgroup).
    /// Typically a quadratic non-residue with small coefficients.
    const ZETA: Self::BaseField;
    /// c1 = g(Z) = Z^3 + A*Z + B
    const C1: Self::BaseField;
    /// c2 = -Z / 2
    const C2: Self::BaseField;
    /// c3 = sqrt(-g(Z) * (3 * Z^2 + 4 * A)) , with parity(c3) == 0
    const C3: Self::BaseField;
    /// c4 = -4 * g(Z) / (3 * Z^2 + 4 * A)
    const C4: Self::BaseField;
}

/// Represents the SVDW hash-to-curve map defined by `P`.
pub struct SVDWMap<P: SVDWConfig>(PhantomData<fn() -> P>);

impl<P: SVDWConfig> SVDWMap<P> {
    /// Compute g(x) = x^3 + A*x + B
    fn evaluate_g(x: P::BaseField) -> P::BaseField {
        let x2 = x.square();
        let x3 = x2 * x;
        x3 + P::COEFF_A * x + P::COEFF_B
    }

    /// Helper for inv0(x) = 1/x if x != 0, else 0
    fn inv0(x: P::BaseField) -> P::BaseField {
        x.inverse().unwrap_or_else(P::BaseField::zero)
    }

    /// Helper for CMOV(a, b, c) = b if c else a
    fn cmov(if_false: P::BaseField, if_true: P::BaseField, signal: bool) -> P::BaseField {
        let mask = P::BaseField::from(signal as u32);
        mask * if_true + (P::BaseField::ONE - mask) * if_false
    }

    fn is_square(x: &P::BaseField) -> bool {
        x.legendre().is_qr()
    }
}

impl<P: SVDWConfig> MapToCurve<Projective<P>> for SVDWMap<P> {
    /// Checks if `P` represents a valid map.
    fn check_parameters() -> Result<(), HashToCurveError> {
        // Base checks from original code
        debug_assert!(
            P::ZETA.legendre().is_qnr(),
            "ZETA must be quadratic non-residue for SVDW"
        );
        debug_assert!(!P::ZETA.is_zero(), "ZETA must be non-zero");
        debug_assert!(!P::COEFF_A.is_zero(), "Coefficient A must be non-zero");
        debug_assert!(!P::COEFF_B.is_zero(), "Coefficient B must be non-zero");

        // c1 = g(Z)
        let g_z = Self::evaluate_g(P::ZETA);
        debug_assert_eq!(P::C1, g_z, "C1 != g(Z)");

        // c2 = -Z / 2
        let two = P::BaseField::from(2u64);
        let two_inv = two.inverse().expect("Field characteristic should not be 2");
        let neg_z_div_2 = -P::ZETA * two_inv;
        debug_assert_eq!(P::C2, neg_z_div_2, "C2 != -Z / 2");

        // Denominator for c3 and c4: d = 3 * Z^2 + 4 * A
        let three = P::BaseField::from(3u64);
        let four = P::BaseField::from(4u64);
        let z2 = P::ZETA.square();
        let den = three * z2 + four * P::COEFF_A;
        debug_assert!(!den.is_zero(), "Denominator (3*Z^2 + 4*A) is zero");

        // c3 = sqrt(-g(Z) * den)
        // We check c3^2 == -g(Z) * den
        let neg_gz_den = -g_z * den;
        debug_assert!(
            neg_gz_den.legendre().is_qr(),
            "Argument for C3 sqrt must be square"
        );
        debug_assert_eq!(P::C3.square(), neg_gz_den, "C3^2 != -g(Z)*(3*Z^2+4*A)");
        debug_assert!(!parity(&P::C3), "parity(C3) must be false");

        // c4 = -4 * g(Z) / den
        let den_inv = den.inverse().expect("Denominator already checked non-zero");
        let neg_four_gz_div_den = -four * g_z * den_inv;
        debug_assert_eq!(P::C4, neg_four_gz_div_den, "C4 != -4*g(Z)/(3*Z^2+4*A)");

        Ok(())
    }

    /// Map an arbitrary base field element to a curve point using SVDW.
    /// Based on IETF draft-irtf-cfrg-hash-to-curve-16, Section 6.6.1.
    /// <https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16#section-6.6.1>
    fn map_to_curve(u: P::BaseField) -> Result<Affine<P>, HashToCurveError> {
        // 1.  tv1 = u^2
        let mut tv1 = u.square();
        // 2.  tv1 = tv1 * c1
        tv1 *= P::C1;
        // 3.  tv2 = 1 + tv1
        let tv2 = P::BaseField::one() + tv1;
        // 4.  tv1 = 1 - tv1
        tv1 = P::BaseField::one() - tv1;
        // 5.  tv3 = tv1 * tv2
        let mut tv3 = tv1 * tv2;
        // 6.  tv3 = inv0(tv3)
        tv3 = Self::inv0(tv3);
        // 7.  tv4 = u * tv1
        let mut tv4 = u * tv1;
        // 8.  tv4 = tv4 * tv3
        tv4 *= tv3;
        // 9.  tv4 = tv4 * c3
        tv4 *= P::C3;
        // 10.  x1 = c2 - tv4
        let x1 = P::C2 - tv4;
        // 11. gx1 = x1^2
        let mut gx1 = x1.square();
        // 12. gx1 = gx1 + A
        gx1 += P::COEFF_A;
        // 13. gx1 = gx1 * x1
        gx1 *= x1;
        // 14. gx1 = gx1 + B
        gx1 += P::COEFF_B;
        // 15.  e1 = is_square(gx1)
        let e1 = Self::is_square(&gx1);
        // 16.  x2 = c2 + tv4
        let x2 = P::C2 + tv4;
        // 17. gx2 = x2^2
        let mut gx2 = x2.square();
        // 18. gx2 = gx2 + A
        gx2 += P::COEFF_A;
        // 19. gx2 = gx2 * x2
        gx2 *= x2;
        // 20. gx2 = gx2 + B
        gx2 += P::COEFF_B;
        // 21.  e2 = is_square(gx2) AND NOT e1 # Avoid short-circuit logic ops
        #[allow(clippy::needless_bitwise_bool)]
        let e2 = Self::is_square(&gx2) & !e1;
        // 22.  x3 = tv2^2
        let mut x3 = tv2.square();
        // 23.  x3 = x3 * tv3
        x3 *= tv3;
        // 24.  x3 = x3^2
        x3.square_in_place();
        // 25.  x3 = x3 * c4
        x3 *= P::C4;
        // 26.  x3 = x3 + Z
        x3 += P::ZETA;
        // 27.   x = CMOV(x3, x1, e1)   # x = x1 if gx1 is square, else x = x3
        let mut x = Self::cmov(x3, x1, e1);
        // 28.   x = CMOV(x, x2, e2)    # x = x2 if gx2 is square and gx1 is not
        x = Self::cmov(x, x2, e2);
        // 29.  gx = x^2
        let mut gx = x.square();
        // 30.  gx = gx + A
        gx += P::COEFF_A;
        // 31.  gx = gx * x
        gx *= x;
        // 32.  gx = gx + B
        gx += P::COEFF_B;
        // 33.   y = sqrt(gx)
        let mut y = gx.sqrt().expect("gx must be a quadratic residue");
        // 34.  e3 = sgn0(u) == sgn0(y)
        let e3 = parity(&u) == parity(&y);
        // 35.   y = CMOV(-y, y, e3)       # Select correct sign of y
        y = Self::cmov(y, -y, e3);
        // 36. return (x, y)
        let point_on_curve = Affine::new_unchecked(x, y);
        debug_assert!(
            point_on_curve.is_on_curve(),
            "SVDW mapped to a point off the curve: (x, y) = ({:?}, {:?}) for input u = {:?}",
            x,
            y,
            u
        );
        Ok(point_on_curve)
    }
}

#[cfg(test)]
mod test {
    #[cfg(all(
        target_has_atomic = "8",
        target_has_atomic = "16",
        target_has_atomic = "32",
        target_has_atomic = "64",
        target_has_atomic = "ptr"
    ))]
    type DefaultHasher = ahash::AHasher;

    #[cfg(not(all(
        target_has_atomic = "8",
        target_has_atomic = "16",
        target_has_atomic = "32",
        target_has_atomic = "64",
        target_has_atomic = "ptr"
    )))]
    type DefaultHasher = fnv::FnvHasher;

    use crate::{
        hashing::{map_to_curve_hasher::MapToCurveBasedHasher, HashToCurve},
        CurveConfig,
    };
    use ark_ff::field_hashers::DefaultFieldHasher;
    use ark_std::vec::*;

    use super::*;
    use ark_ff::{fields::Fp64, MontBackend, MontFp};
    use hashbrown::HashMap;
    use sha2::Sha256;

    #[derive(ark_ff::MontConfig)]
    #[modulus = "127"]
    #[generator = "6"]
    pub(crate) struct F127Config;
    pub(crate) type F127 = Fp64<MontBackend<F127Config, 1>>;

    const F127_ONE: F127 = MontFp!("1");

    struct TestSVDWMapToCurveConfig;

    impl CurveConfig for TestSVDWMapToCurveConfig {
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
    impl SWCurveConfig for TestSVDWMapToCurveConfig {
        /// COEFF_A = 1
        const COEFF_A: F127 = F127_ONE;

        /// COEFF_B = 63
        const COEFF_B: F127 = MontFp!("63");

        /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
        const GENERATOR: Affine<Self> = Affine::new_unchecked(MontFp!("62"), MontFp!("70"));
    }

    impl SVDWConfig for TestSVDWMapToCurveConfig {
        const ZETA: F127 = MontFp!("-1");
        const C1: F127 = MontFp!("61");
        const C2: F127 = MontFp!("64");
        const C3: F127 = MontFp!("118");
        const C4: F127 = MontFp!("74");
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
    fn hash_arbitrary_string_to_curve_svdw() {
        let test_swu_to_curve_hasher = MapToCurveBasedHasher::<
            Projective<TestSVDWMapToCurveConfig>,
            DefaultFieldHasher<Sha256, 128>,
            SVDWMap<TestSVDWMapToCurveConfig>,
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
    fn map_field_to_curve_svdw() {
        SVDWMap::<TestSVDWMapToCurveConfig>::check_parameters().unwrap();

        let mut map_range: Vec<Affine<TestSVDWMapToCurveConfig>> = vec![];
        for current_field_element in 0..127 {
            let element = F127::from(current_field_element as u64);
            map_range.push(SVDWMap::map_to_curve(element).unwrap());
        }

        let mut counts =
            HashMap::with_hasher(core::hash::BuildHasherDefault::<DefaultHasher>::default());

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
