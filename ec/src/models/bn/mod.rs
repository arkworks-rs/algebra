use crate::{
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
    PairingEngine,
};
use ark_ff::{
    fields::{
        fp12_2over3over2::{Fp12, Fp12Config},
        fp2::Fp2Config,
        fp6_3over2::Fp6Config,
        Field, Fp2, PrimeField,
    },
    CyclotomicMultSubgroup,
};
use num_traits::One;

use core::marker::PhantomData;

pub enum TwistType {
    M,
    D,
}

pub trait BnParameters: 'static {
    /// The absolute value of the BN curve parameter `X`
    /// (as in `q = 36 X^4 + 36 X^3 + 24 X^2 + 6 X + 1`).
    const X: &'static [u64];

    /// Whether or not `X` is negative.
    const X_IS_NEGATIVE: bool;

    /// The absolute value of `6X + 2`.
    const ATE_LOOP_COUNT: &'static [i8];

    const TWIST_TYPE: TwistType;
    const TWIST_MUL_BY_Q_X: Fp2<Self::Fp2Config>;
    const TWIST_MUL_BY_Q_Y: Fp2<Self::Fp2Config>;
    type Fp: PrimeField + Into<<Self::Fp as PrimeField>::BigInt>;
    type Fp2Config: Fp2Config<Fp = Self::Fp>;
    type Fp6Config: Fp6Config<Fp2Config = Self::Fp2Config>;
    type Fp12Config: Fp12Config<Fp6Config = Self::Fp6Config>;
    type G1Parameters: SWCurveConfig<BaseField = Self::Fp>;
    type G2Parameters: SWCurveConfig<
        BaseField = Fp2<Self::Fp2Config>,
        ScalarField = <Self::G1Parameters as CurveConfig>::ScalarField,
    >;
}

pub mod g1;
pub mod g2;

pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};

#[derive(Derivative)]
#[derivative(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct Bn<P: BnParameters>(PhantomData<fn() -> P>);

impl<P: BnParameters> Bn<P> {
    /// Evaluates the line function at point p.
    fn ell(f: &mut Fp12<P::Fp12Config>, coeffs: &g2::EllCoeff<Fp2<P::Fp2Config>>, p: &G1Affine<P>) {
        let mut c0 = coeffs.0;
        let mut c1 = coeffs.1;
        let mut c2 = coeffs.2;

        match P::TWIST_TYPE {
            TwistType::M => {
                c2.mul_assign_by_fp(&p.y);
                c1.mul_assign_by_fp(&p.x);
                f.mul_by_014(&c0, &c1, &c2);
            },
            TwistType::D => {
                c0.mul_assign_by_fp(&p.y);
                c1.mul_assign_by_fp(&p.x);
                f.mul_by_034(&c0, &c1, &c2);
            },
        }
    }

    fn exp_by_neg_x(mut f: Fp12<P::Fp12Config>) -> Fp12<P::Fp12Config> {
        f = f.cyclotomic_exp(&P::X);
        if !P::X_IS_NEGATIVE {
            f.conjugate();
        }
        f
    }
}

impl<P: BnParameters> PairingEngine for Bn<P> {
    type Fr = <P::G1Parameters as CurveConfig>::ScalarField;
    type G1Projective = G1Projective<P>;
    type G1Affine = G1Affine<P>;
    type G1Prepared = G1Prepared<P>;
    type G2Projective = G2Projective<P>;
    type G2Affine = G2Affine<P>;
    type G2Prepared = G2Prepared<P>;
    type Fq = P::Fp;
    type Fqe = Fp2<P::Fp2Config>;
    type Fqk = Fp12<P::Fp12Config>;

    fn miller_loop<'a, I>(i: I) -> Self::Fqk
    where
        I: IntoIterator<Item = &'a (Self::G1Prepared, Self::G2Prepared)>,
    {
        let mut pairs = vec![];
        for (p, q) in i {
            if !p.is_zero() && !q.is_zero() {
                pairs.push((p, q.ell_coeffs.iter()));
            }
        }

        let mut f = Self::Fqk::one();

        for i in (1..P::ATE_LOOP_COUNT.len()).rev() {
            if i != P::ATE_LOOP_COUNT.len() - 1 {
                f.square_in_place();
            }

            for (p, ref mut coeffs) in &mut pairs {
                Self::ell(&mut f, coeffs.next().unwrap(), &p.0);
            }

            let bit = P::ATE_LOOP_COUNT[i - 1];
            match bit {
                1 => {
                    for &mut (p, ref mut coeffs) in &mut pairs {
                        Self::ell(&mut f, coeffs.next().unwrap(), &p.0);
                    }
                },
                -1 => {
                    for &mut (p, ref mut coeffs) in &mut pairs {
                        Self::ell(&mut f, coeffs.next().unwrap(), &p.0);
                    }
                },
                _ => continue,
            }
        }

        if P::X_IS_NEGATIVE {
            f.conjugate();
        }

        for &mut (p, ref mut coeffs) in &mut pairs {
            Self::ell(&mut f, coeffs.next().unwrap(), &p.0);
        }

        for &mut (p, ref mut coeffs) in &mut pairs {
            Self::ell(&mut f, coeffs.next().unwrap(), &p.0);
        }

        f
    }

    #[allow(clippy::let_and_return)]
    fn final_exponentiation(f: &Self::Fqk) -> Option<Self::Fqk> {
        // Easy part: result = elt^((q^6-1)*(q^2+1)).
        // Follows, e.g., Beuchat et al page 9, by computing result as follows:
        //   elt^((q^6-1)*(q^2+1)) = (conj(elt) * elt^(-1))^(q^2+1)

        // f1 = r.conjugate() = f^(p^6)
        let mut f1 = *f;
        f1.conjugate();

        f.inverse().map(|mut f2| {
            // f2 = f^(-1);
            // r = f^(p^6 - 1)
            let mut r = f1 * &f2;

            // f2 = f^(p^6 - 1)
            f2 = r;
            // r = f^((p^6 - 1)(p^2))
            r.frobenius_map(2);

            // r = f^((p^6 - 1)(p^2) + (p^6 - 1))
            // r = f^((p^6 - 1)(p^2 + 1))
            r *= &f2;

            // Hard part follows Laura Fuentes-Castaneda et al. "Faster hashing to G2"
            // by computing:
            //
            // result = elt^(q^3 * (12*z^3 + 6z^2 + 4z - 1) +
            //               q^2 * (12*z^3 + 6z^2 + 6z) +
            //               q   * (12*z^3 + 6z^2 + 4z) +
            //               1   * (12*z^3 + 12z^2 + 6z + 1))
            // which equals
            //
            // result = elt^( 2z * ( 6z^2 + 3z + 1 ) * (q^4 - q^2 + 1)/r ).

            let y0 = Self::exp_by_neg_x(r);
            let y1 = y0.cyclotomic_square();
            let y2 = y1.cyclotomic_square();
            let mut y3 = y2 * &y1;
            let y4 = Self::exp_by_neg_x(y3);
            let y5 = y4.cyclotomic_square();
            let mut y6 = Self::exp_by_neg_x(y5);
            y3.conjugate();
            y6.conjugate();
            let y7 = y6 * &y4;
            let mut y8 = y7 * &y3;
            let y9 = y8 * &y1;
            let y10 = y8 * &y4;
            let y11 = y10 * &r;
            let mut y12 = y9;
            y12.frobenius_map(1);
            let y13 = y12 * &y11;
            y8.frobenius_map(2);
            let y14 = y8 * &y13;
            r.conjugate();
            let mut y15 = r * &y9;
            y15.frobenius_map(3);
            let y16 = y15 * &y14;

            y16
        })
    }
}
