use crate::{
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
    pairing::{MillerLoopOutput, Pairing, PairingOutput},
    AffineRepr,
};
use ark_ff::{
    fields::{
        fp12_2over3over2::{Fp12, Fp12Config},
        fp2::Fp2Config,
        fp6_3over2::Fp6Config,
        Fp2,
    },
    BitIteratorBE, CyclotomicMultSubgroup, Field, PrimeField,
};
use ark_std::{marker::PhantomData, vec::Vec};
use num_traits::{One, Zero};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// A particular BLS12 group can have G2 being either a multiplicative or a
/// divisive twist.
pub enum TwistType {
    M,
    D,
}

pub trait Bls12Config: 'static + Sized {
    /// Parameterizes the BLS12 family.
    const X: &'static [u64];
    /// Is `Self::X` negative?
    const X_IS_NEGATIVE: bool;
    /// What kind of twist is this?
    const TWIST_TYPE: TwistType;

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
    ) -> MillerLoopOutput<Bls12<Self>> {
        use itertools::Itertools;

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
                let mut f = <Bls12<Self> as Pairing>::TargetField::one();
                for i in BitIteratorBE::without_leading_zeros(Self::X).skip(1) {
                    f.square_in_place();
                    for (p, coeffs) in pairs.iter_mut() {
                        Bls12::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                    }
                    if i {
                        for (p, coeffs) in pairs.iter_mut() {
                            Bls12::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                        }
                    }
                }
                f
            })
            .product::<<Bls12<Self> as Pairing>::TargetField>();

        if Self::X_IS_NEGATIVE {
            f.cyclotomic_inverse_in_place();
        }
        MillerLoopOutput(f)
    }

    fn final_exponentiation(
        f: MillerLoopOutput<Bls12<Self>>,
    ) -> Option<PairingOutput<Bls12<Self>>> {
        // Computing the final exponentation following
        // https://eprint.iacr.org/2020/875
        // Adapted from the implementation in https://github.com/ConsenSys/gurvy/pull/29

        // f1 = r.cyclotomic_inverse_in_place() = f^(p^6)
        let f = f.0;
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

            // Hard part of the final exponentation:
            // t[0].CyclotomicSquare(&result)
            let mut y0 = r.cyclotomic_square();
            // t[1].Expt(&result)
            let mut y1 = Fp12::zero();
            Bls12::<Self>::exp_by_x(&r, &mut y1);
            // t[2].InverseUnitary(&result)
            let mut y2 = r;
            y2.cyclotomic_inverse_in_place();
            // t[1].Mul(&t[1], &t[2])
            y1 *= &y2;
            // t[2].Expt(&t[1])
            Bls12::<Self>::exp_by_x(&y1, &mut y2);
            // t[1].InverseUnitary(&t[1])
            y1.cyclotomic_inverse_in_place();
            // t[1].Mul(&t[1], &t[2])
            y1 *= &y2;
            // t[2].Expt(&t[1])
            Bls12::<Self>::exp_by_x(&y1, &mut y2);
            // t[1].Frobenius(&t[1])
            y1.frobenius_map_in_place(1);
            // t[1].Mul(&t[1], &t[2])
            y1 *= &y2;
            // result.Mul(&result, &t[0])
            r *= &y0;
            // t[0].Expt(&t[1])
            Bls12::<Self>::exp_by_x(&y1, &mut y0);
            // t[2].Expt(&t[0])
            Bls12::<Self>::exp_by_x(&y0, &mut y2);
            // t[0].FrobeniusSquare(&t[1])
            y0 = y1;
            y0.frobenius_map_in_place(2);
            // t[1].InverseUnitary(&t[1])
            y1.cyclotomic_inverse_in_place();
            // t[1].Mul(&t[1], &t[2])
            y1 *= &y2;
            // t[1].Mul(&t[1], &t[0])
            y1 *= &y0;
            // result.Mul(&result, &t[1])
            r *= &y1;
            PairingOutput(r)
        })
    }
}

pub mod g1;
pub mod g2;

pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};

#[derive(Derivative)]
#[derivative(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct Bls12<P: Bls12Config>(PhantomData<fn() -> P>);

impl<P: Bls12Config> Bls12<P> {
    // Evaluate the line function at point p.
    fn ell(f: &mut Fp12<P::Fp12Config>, coeffs: &g2::EllCoeff<P>, p: &G1Affine<P>) {
        let mut c0 = coeffs.0;
        let mut c1 = coeffs.1;
        let mut c2 = coeffs.2;
        let (px, py) = p.xy().unwrap();

        match P::TWIST_TYPE {
            TwistType::M => {
                c2.mul_assign_by_fp(py);
                c1.mul_assign_by_fp(px);
                f.mul_by_014(&c0, &c1, &c2);
            },
            TwistType::D => {
                c0.mul_assign_by_fp(py);
                c1.mul_assign_by_fp(px);
                f.mul_by_034(&c0, &c1, &c2);
            },
        }
    }

    // Exponentiates `f` by `Self::X`, and stores the result in `result`.
    fn exp_by_x(f: &Fp12<P::Fp12Config>, result: &mut Fp12<P::Fp12Config>) {
        *result = f.cyclotomic_exp(P::X);
        if P::X_IS_NEGATIVE {
            result.cyclotomic_inverse_in_place();
        }
    }
}

impl<P: Bls12Config> Pairing for Bls12<P> {
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
