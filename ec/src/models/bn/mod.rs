use crate::{
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
    pairing::{MillerLoopOutput, Pairing, PairingOutput},
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
use ark_std::{cfg_chunks_mut, marker::PhantomData, vec::*};
use educe::Educe;
use itertools::Itertools;
use num_traits::One;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub enum TwistType {
    M,
    D,
}

pub trait BnConfig: 'static + Sized {
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
    type G1Config: SWCurveConfig<BaseField = Self::Fp>;
    type G2Config: SWCurveConfig<
        BaseField = Fp2<Self::Fp2Config>,
        ScalarField = <Self::G1Config as CurveConfig>::ScalarField,
    >;

    fn multi_miller_loop(
        a: impl IntoIterator<Item = impl Into<G1Prepared<Self>>>,
        b: impl IntoIterator<Item = impl Into<G2Prepared<Self>>>,
    ) -> MillerLoopOutput<Bn<Self>> {
        let mut pairs = a
            .into_iter()
            .zip_eq(b)
            .filter_map(|(p, q)| {
                let (p, q) = (p.into(), q.into());
                match !p.is_zero() && !q.is_zero() {
                    true => Some((p, q.ell_coeffs.into_iter())),
                    false => None,
                }
            })
            .collect::<Vec<_>>();

        let mut f = cfg_chunks_mut!(pairs, 4)
            .map(|pairs| {
                let mut f = <Bn<Self> as Pairing>::TargetField::one();
                for i in (1..Self::ATE_LOOP_COUNT.len()).rev() {
                    if i != Self::ATE_LOOP_COUNT.len() - 1 {
                        f.square_in_place();
                    }

                    for (p, coeffs) in pairs.iter_mut() {
                        Bn::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                    }

                    let bit = Self::ATE_LOOP_COUNT[i - 1];
                    if bit == 1 || bit == -1 {
                        for (p, coeffs) in pairs.iter_mut() {
                            Bn::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                        }
                    }
                }
                f
            })
            .product::<<Bn<Self> as Pairing>::TargetField>();

        if Self::X_IS_NEGATIVE {
            f.cyclotomic_inverse_in_place();
        }

        for (p, coeffs) in &mut pairs {
            Bn::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
        }

        for (p, coeffs) in &mut pairs {
            Bn::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
        }

        MillerLoopOutput(f)
    }

    #[allow(clippy::let_and_return)]
    fn final_exponentiation(f: MillerLoopOutput<Bn<Self>>) -> Option<PairingOutput<Bn<Self>>> {
        // Easy part: result = elt^((q^6-1)*(q^2+1)).
        // Follows, e.g., Beuchat et al page 9, by computing result as follows:
        //   elt^((q^6-1)*(q^2+1)) = (conj(elt) * elt^(-1))^(q^2+1)
        let f = f.0;

        // f1 = r.cyclotomic_inverse_in_place() = f^(p^6)
        let mut f1 = f;
        f1.cyclotomic_inverse_in_place();

        f.inverse().map(|mut f2| {
            // f2 = f^(-1);
            // r = f^(p^6 - 1)
            let mut r = f1 * &f2;

            // f2 = f^(p^6 - 1)
            f2 = r;
            // r = f^((p^6 - 1)(p^2))
            r.frobenius_map_in_place(2);

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

            let y0 = Bn::<Self>::exp_by_neg_x(r);
            let y1 = y0.cyclotomic_square();
            let y2 = y1.cyclotomic_square();
            let mut y3 = y2 * &y1;
            let y4 = Bn::<Self>::exp_by_neg_x(y3);
            let y5 = y4.cyclotomic_square();
            let mut y6 = Bn::<Self>::exp_by_neg_x(y5);
            y3.cyclotomic_inverse_in_place();
            y6.cyclotomic_inverse_in_place();
            let y7 = y6 * &y4;
            let mut y8 = y7 * &y3;
            let y9 = y8 * &y1;
            let y10 = y8 * &y4;
            let y11 = y10 * &r;
            let mut y12 = y9;
            y12.frobenius_map_in_place(1);
            let y13 = y12 * &y11;
            y8.frobenius_map_in_place(2);
            let y14 = y8 * &y13;
            r.cyclotomic_inverse_in_place();
            let mut y15 = r * &y9;
            y15.frobenius_map_in_place(3);
            let y16 = y15 * &y14;

            PairingOutput(y16)
        })
    }
}

pub mod g1;
pub mod g2;

pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};

#[derive(Educe)]
#[educe(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct Bn<P: BnConfig>(PhantomData<fn() -> P>);

impl<P: BnConfig> Bn<P> {
    /// Evaluates the line function at point p.
    fn ell(f: &mut Fp12<P::Fp12Config>, coeffs: &g2::EllCoeff<P>, p: &G1Affine<P>) {
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
        f = f.cyclotomic_exp(P::X);
        if !P::X_IS_NEGATIVE {
            f.cyclotomic_inverse_in_place();
        }
        f
    }
}

impl<P: BnConfig> Pairing for Bn<P> {
    type BaseField = <P::G1Config as CurveConfig>::BaseField;
    type ScalarField = <P::G1Config as CurveConfig>::ScalarField;
    type G1 = G1Projective<P>;
    type G1Affine = G1Affine<P>;
    type G1Prepared = G1Prepared<P>;
    type G2 = G2Projective<P>;
    type G2Affine = G2Affine<P>;
    type G2Prepared = G2Prepared<P>;
    type TargetField = Fp12<P::Fp12Config>;

    fn multi_miller_loop(
        a: impl IntoIterator<Item = impl Into<Self::G1Prepared>>,
        b: impl IntoIterator<Item = impl Into<Self::G2Prepared>>,
    ) -> MillerLoopOutput<Self> {
        P::multi_miller_loop(a, b)
    }

    fn final_exponentiation(f: MillerLoopOutput<Self>) -> Option<PairingOutput<Self>> {
        P::final_exponentiation(f)
    }
}
