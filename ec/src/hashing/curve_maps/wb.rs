use core::marker::PhantomData;

use crate::{models::short_weierstrass::SWCurveConfig, CurveConfig};
use ark_ff::batch_inversion;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};

use crate::{
    hashing::{map_to_curve_hasher::MapToCurve, HashToCurveError},
    models::short_weierstrass::{Affine, Projective},
    AffineRepr,
};

use super::swu::{SWUConfig, SWUMap};
type BaseField<MP> = <MP as CurveConfig>::BaseField;

/// [`IsogenyMap`] defines an isogeny between curves of
/// form `Phi(x, y) := (a(x), b(x)*y).
/// The `x` coordinate of the codomain point only depends on the
/// `x`-coordinate of the domain point, and the
/// `y`-coordinate of the codomain point is a multiple of the `y`-coordinate of the domain point.
/// The multiplier depends on the `x`-coordinate of the domain point.
/// All isogeny maps of curves of short Weierstrass form can be written in this way. See
/// [\[Ga18]\]. Theorem 9.7.5 for details.
///
/// We assume that `Domain` and `Codomain` have the same `BaseField` but we use both
/// `BaseField<Domain>` and `BaseField<Codomain>` in our fields' definitions to avoid
/// using `PhantomData`
///
/// - [\[Ga18]\] Galbraith, S. D. (2018). Mathematics of public key cryptography.
pub struct IsogenyMap<
    'a,
    Domain: SWCurveConfig,
    Codomain: SWCurveConfig<BaseField = BaseField<Domain>>,
> {
    pub x_map_numerator: &'a [BaseField<Domain>],
    pub x_map_denominator: &'a [BaseField<Codomain>],

    pub y_map_numerator: &'a [BaseField<Domain>],
    pub y_map_denominator: &'a [BaseField<Codomain>],
}

impl<'a, Domain, Codomain> IsogenyMap<'a, Domain, Codomain>
where
    Domain: SWCurveConfig,
    Codomain: SWCurveConfig<BaseField = BaseField<Domain>>,
{
    fn apply(&self, domain_point: Affine<Domain>) -> Result<Affine<Codomain>, HashToCurveError> {
        match domain_point.xy() {
            Some((x, y)) => {
                let x_num = DensePolynomial::from_coefficients_slice(self.x_map_numerator);
                let x_den = DensePolynomial::from_coefficients_slice(self.x_map_denominator);

                let y_num = DensePolynomial::from_coefficients_slice(self.y_map_numerator);
                let y_den = DensePolynomial::from_coefficients_slice(self.y_map_denominator);

                let mut v: [BaseField<Domain>; 2] = [x_den.evaluate(&x), y_den.evaluate(&x)];
                batch_inversion(&mut v);
                let img_x = x_num.evaluate(&x) * v[0];
                let img_y = (y_num.evaluate(&x) * y) * v[1];
                Ok(Affine::<Codomain>::new_unchecked(img_x, img_y))
            },
            None => Ok(Affine::identity()),
        }
    }
}

/// Trait defining the necessary parameters for the WB hash-to-curve method
/// for the curves of Weierstrass form of:
/// of y^2 = x^3 + a*x + b where b != 0 but `a` can be zero like BLS-381 curve.
/// From [\[WB2019\]]
///
/// - [\[WB2019\]] <http://dx.doi.org/10.46586/tches.v2019.i4.154-179>
pub trait WBConfig: SWCurveConfig + Sized {
    // The isogenous curve should be defined over the same base field but it can have
    // different scalar field type IsogenousCurveScalarField :
    type IsogenousCurve: SWUConfig<BaseField = BaseField<Self>>;

    const ISOGENY_MAP: IsogenyMap<'static, Self::IsogenousCurve, Self>;
}

pub struct WBMap<P: WBConfig> {
    swu_field_curve_hasher: PhantomData<SWUMap<P::IsogenousCurve>>,
    curve_params: PhantomData<fn() -> P>,
}

impl<P: WBConfig> MapToCurve<Projective<P>> for WBMap<P> {
    /// Checks if `P` represents a valid map.
    fn check_parameters() -> Result<(), HashToCurveError> {
        match P::ISOGENY_MAP.apply(P::IsogenousCurve::GENERATOR) {
            Ok(point_on_curve) => {
                debug_assert!(point_on_curve.is_on_curve(),
			      "the isogeny maps the generator of its domain: {} into {} which does not belong to its codomain.",P::IsogenousCurve::GENERATOR, point_on_curve);
            },
            Err(e) => return Err(e),
        }

        SWUMap::<P::IsogenousCurve>::check_parameters().unwrap(); // Or ?
        Ok(())
    }

    /// Map random field point to a random curve point
    /// inspired from
    /// <https://github.com/zcash/pasta_curves/blob/main/src/hashtocurve.rs>
    fn map_to_curve(
        element: <Affine<P> as AffineRepr>::BaseField,
    ) -> Result<Affine<P>, HashToCurveError> {
        // first we need to map the field point to the isogenous curve
        let point_on_isogenious_curve = SWUMap::<P::IsogenousCurve>::map_to_curve(element).unwrap();
        P::ISOGENY_MAP.apply(point_on_isogenious_curve)
    }
}

#[cfg(test)]
mod test {
    use crate::{
        hashing::{
            curve_maps::{
                swu::SWUConfig,
                wb::{IsogenyMap, WBConfig, WBMap},
            },
            map_to_curve_hasher::MapToCurveBasedHasher,
            HashToCurve,
        },
        models::short_weierstrass::SWCurveConfig,
        short_weierstrass::{Affine, Projective},
        CurveConfig,
    };
    use ark_ff::{field_hashers::DefaultFieldHasher, fields::Fp64, MontBackend, MontFp};

    #[derive(ark_ff::MontConfig)]
    #[modulus = "127"]
    #[generator = "6"]
    pub struct F127Config;
    pub type F127 = Fp64<MontBackend<F127Config, 1>>;

    const F127_ZERO: F127 = MontFp!("0");
    const F127_ONE: F127 = MontFp!("1");

    /// The struct defining our parameters for the target curve of hashing
    struct TestWBF127MapToCurveConfig;

    impl CurveConfig for TestWBF127MapToCurveConfig {
        const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
        const COFACTOR_INV: F127 = F127_ONE;

        type BaseField = F127;
        type ScalarField = F127;
    }

    /// E: Elliptic Curve defined by y^2 = x^3 + 3 over Finite
    /// Field of size 127
    impl SWCurveConfig for TestWBF127MapToCurveConfig {
        /// COEFF_A = 0
        const COEFF_A: F127 = F127_ZERO;

        /// COEFF_B = 3
    #[rustfmt::skip]
        const COEFF_B: F127 = MontFp!("3");

        /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
        const GENERATOR: Affine<Self> = Affine::new_unchecked(MontFp!("62"), MontFp!("70"));
    }

    /// Testing WB19 hashing on a small curve
    /// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite
    /// Field of size 127
    /// Isogenous to E : y^2 = x^3 + 3
    struct TestSWU127MapToIsogenousCurveConfig;

    /// First we define the isogenous curve
    /// sage: E_isogenous.order()
    /// 127
    impl CurveConfig for TestSWU127MapToIsogenousCurveConfig {
        const COFACTOR: &'static [u64] = &[1];

    #[rustfmt::skip]
        const COFACTOR_INV: F127 = F127_ONE;

        type BaseField = F127;
        type ScalarField = F127;
    }

    /// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite
    /// Field of size 127
    impl SWCurveConfig for TestSWU127MapToIsogenousCurveConfig {
        /// COEFF_A = 109
        const COEFF_A: F127 = MontFp!("109");

        /// COEFF_B = 124
    #[rustfmt::skip]
        const COEFF_B: F127 = MontFp!("124");

        /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
        const GENERATOR: Affine<Self> = Affine::new_unchecked(MontFp!("84"), MontFp!("2"));
    }

    /// SWU parameters for E_isogenous
    impl SWUConfig for TestSWU127MapToIsogenousCurveConfig {
        /// NON-SQUARE = - 1
        const ZETA: F127 = MontFp!("-1");
    }

    /// E_isogenous : Elliptic Curve defined by y^2 = x^3 + 109*x + 124 over Finite
    /// Field of size 127
    /// With psi: E_isogenous -> E
    /// psi = (psi_x(x,y), psi_y(x,y))
    /// where
    /// psi_x: (-57*x^13 - 21*x^12 + 10*x^11 + 34*x^10 + 40*x^9 -
    /// 13*x^8 + 32*x^7 - 32*x^6 + 23*x^5 - 14*x^4 + 39*x^3 + 23*x^2 + 63*x +
    /// 4)/(x^12 - 13*x^11 + 11*x^10 - 33*x^9 - 30*x^8 + 30*x^7 + 34*x^6 - 44*x^5 +
    /// 63*x^4 - 20*x^3 - 10*x^2 + 31*x + 2)
    ///
    /// psi_y: (10*x^18*y + 59*x^17*y + 41*x^16*y + 48*x^15*y - 7*x^14*y + 6*x^13*y +
    /// 5*x^12*y + 62*x^11*y + 12*x^10*y + 36*x^9*y - 49*x^8*y - 18*x^7*y - 63*x^6*y
    /// - 43*x^5*y - 60*x^4*y - 18*x^3*y + 30*x^2*y - 57*x*y - 34*y)/(x^18 + 44*x^17
    /// - 63*x^16 + 52*x^15 + 3*x^14 + 38*x^13 - 30*x^12 + 11*x^11 - 42*x^10 - 13*x^9
    /// - 46*x^8 - 61*x^7 - 16*x^6 - 55*x^5 + 18*x^4 + 23*x^3 - 24*x^2 - 18*x + 32)
    const ISOGENY_MAP_TESTWBF127: IsogenyMap<
        '_,
        TestSWU127MapToIsogenousCurveConfig,
        TestWBF127MapToCurveConfig,
    > = IsogenyMap {
        x_map_numerator: &[
            MontFp!("4"),
            MontFp!("63"),
            MontFp!("23"),
            MontFp!("39"),
            MontFp!("-14"),
            MontFp!("23"),
            MontFp!("-32"),
            MontFp!("32"),
            MontFp!("-13"),
            MontFp!("40"),
            MontFp!("34"),
            MontFp!("10"),
            MontFp!("-21"),
            MontFp!("-57"),
        ],

        x_map_denominator: &[
            MontFp!("2"),
            MontFp!("31"),
            MontFp!("-10"),
            MontFp!("-20"),
            MontFp!("63"),
            MontFp!("-44"),
            MontFp!("34"),
            MontFp!("30"),
            MontFp!("-30"),
            MontFp!("-33"),
            MontFp!("11"),
            MontFp!("-13"),
            MontFp!("1"),
        ],

        y_map_numerator: &[
            MontFp!("-34"),
            MontFp!("-57"),
            MontFp!("30"),
            MontFp!("-18"),
            MontFp!("-60"),
            MontFp!("-43"),
            MontFp!("-63"),
            MontFp!("-18"),
            MontFp!("-49"),
            MontFp!("36"),
            MontFp!("12"),
            MontFp!("62"),
            MontFp!("5"),
            MontFp!("6"),
            MontFp!("-7"),
            MontFp!("48"),
            MontFp!("41"),
            MontFp!("59"),
            MontFp!("10"),
        ],

        y_map_denominator: &[
            MontFp!("32"),
            MontFp!("-18"),
            MontFp!("-24"),
            MontFp!("23"),
            MontFp!("18"),
            MontFp!("-55"),
            MontFp!("-16"),
            MontFp!("-61"),
            MontFp!("-46"),
            MontFp!("-13"),
            MontFp!("-42"),
            MontFp!("11"),
            MontFp!("-30"),
            MontFp!("38"),
            MontFp!("3"),
            MontFp!("52"),
            MontFp!("-63"),
            MontFp!("44"),
            MontFp!("1"),
        ],
    };
    impl WBConfig for TestWBF127MapToCurveConfig {
        type IsogenousCurve = TestSWU127MapToIsogenousCurveConfig;

        const ISOGENY_MAP: super::IsogenyMap<'static, Self::IsogenousCurve, Self> =
            ISOGENY_MAP_TESTWBF127;
    }

    /// The point of the test is to get a simple WB compatible curve
    /// and make simple hash
    #[test]
    fn hash_arbitrary_string_to_curve_wb() {
        use sha2::Sha256;
        let test_wb_to_curve_hasher = MapToCurveBasedHasher::<
            Projective<TestWBF127MapToCurveConfig>,
            DefaultFieldHasher<Sha256, 128>,
            WBMap<TestWBF127MapToCurveConfig>,
        >::new(&[1])
        .unwrap();

        let hash_result = test_wb_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

        assert!(
            hash_result.x != F127_ZERO && hash_result.y != F127_ZERO,
            "we assume that not both a and b coefficienst are zero for the test curve"
        );

        assert!(
            hash_result.is_on_curve(),
            "hash results into a point off the curve"
        );
    }
}
