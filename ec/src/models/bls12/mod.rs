use crate::{
    models::{ModelParameters, SWModelParameters},
    pairing::{MillerLoopOutput, Pairing, PairingOutput},
};
use ark_ff::fields::{
    fp12_2over3over2::{Fp12, Fp12Parameters},
    fp2::Fp2Parameters,
    fp6_3over2::Fp6Parameters,
    BitIteratorBE, CyclotomicField, Field, Fp2, PrimeField, SquareRootField,
};
use core::marker::PhantomData;
use num_traits::{One, Zero};

use ark_std::cfg_iter;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// A particular BLS12 group can have G2 being either a multiplicative or a
/// divisive twist.
pub enum TwistType {
    M,
    D,
}

pub trait Bls12Parameters: 'static {
    /// Parameterizes the BLS12 family.
    const X: &'static [u64];
    /// Is `Self::X` negative?
    const X_IS_NEGATIVE: bool;
    /// What kind of twist is this?
    const TWIST_TYPE: TwistType;

    type Fp: PrimeField + SquareRootField + Into<<Self::Fp as PrimeField>::BigInt>;
    type Fp2Params: Fp2Parameters<Fp = Self::Fp>;
    type Fp6Params: Fp6Parameters<Fp2Params = Self::Fp2Params>;
    type Fp12Params: Fp12Parameters<Fp6Params = Self::Fp6Params>;
    type G1Parameters: SWModelParameters<BaseField = Self::Fp>;
    type G2Parameters: SWModelParameters<
        BaseField = Fp2<Self::Fp2Params>,
        ScalarField = <Self::G1Parameters as ModelParameters>::ScalarField,
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
pub struct Bls12<P: Bls12Parameters>(PhantomData<fn() -> P>);

impl<P: Bls12Parameters> Bls12<P> {
    // Evaluate the line function at point p.
    fn ell(f: &mut Fp12<P::Fp12Params>, coeffs: &g2::EllCoeff<Fp2<P::Fp2Params>>, p: &G1Affine<P>) {
        let mut c0 = coeffs.0;
        let mut c1 = coeffs.1;
        let mut c2 = coeffs.2;

        match P::TWIST_TYPE {
            TwistType::M => {
                c2.mul_assign_by_fp(&p.y());
                c1.mul_assign_by_fp(&p.x());
                f.mul_by_014(&c0, &c1, &c2);
            }
            TwistType::D => {
                c0.mul_assign_by_fp(&p.y());
                c1.mul_assign_by_fp(&p.x());
                f.mul_by_034(&c0, &c1, &c2);
            }
        }
    }

    // Exponentiates `f` by `Self::X`, and stores the result in `result`.
    fn exp_by_x(f: &Fp12<P::Fp12Params>, result: &mut Fp12<P::Fp12Params>) {
        *result = f.cyclotomic_exp(P::X);
        if P::X_IS_NEGATIVE {
            result.cyclotomic_inverse_in_place();
        }
    }
}

impl<P: Bls12Parameters> Pairing for Bls12<P> {
    type ScalarField = <P::G1Parameters as ModelParameters>::ScalarField;
    type G1 = G1Projective<P>;
    type G1Prepared = G1Prepared<P>;
    type G2 = G2Projective<P>;
    type G2Prepared = G2Prepared<P>;
    type TargetField = Fp12<P::Fp12Params>;

    #[must_use]
    fn miller_loop<'a>(
        i: impl IntoIterator<Item = &'a (Self::G1Prepared, Self::G2Prepared)>,
    ) -> MillerLoopOutput<Self> {
        let mut pairs = vec![];
        for (p, q) in i {
            if !p.is_zero() && !q.is_zero() {
                pairs.push((p, &q.ell_coeffs));
            }
        }

        let mut f = cfg_iter!(pairs)
            .map(|(p, q_coeffs)| {
                let mut j = 0;
                let mut f = Self::TargetField::one();
                for i in BitIteratorBE::new(P::X).skip(1) {
                    f.square_in_place();
                    Self::ell(&mut f, &q_coeffs[j], &p.0);
                    j += 1;
                    if i {
                        Self::ell(&mut f, &q_coeffs[j], &p.0);
                        j += 1;
                    }
                }
                f
            })
            .product::<Self::TargetField>();

        if P::X_IS_NEGATIVE {
            f.cyclotomic_inverse_in_place();
        }
        MillerLoopOutput(f)
    }

    fn final_exponentiation(mlo: MillerLoopOutput<Self>) -> Option<PairingOutput<Self>> {
        let f = mlo.0;
        // Computing the final exponentation following
        // https://eprint.iacr.org/2020/875
        // Adapted from the implementation in https://github.com/ConsenSys/gurvy/pull/29

        // f1 = r.cyclotomic_inverse_in_place() = f^(p^6)
        let f1 = f.cyclotomic_inverse()?;
        f.inverse().and_then(|mut f2| {
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

            // Hard part of the final exponentation:
            // t[0].CyclotomicSquare(&result)
            let mut y0 = r.cyclotomic_square();
            // t[1].Expt(&result)
            let mut y1 = Fp12::zero();
            Self::exp_by_x(&r, &mut y1);
            // t[2].InverseUnitary(&result)
            let mut y2 = r.cyclotomic_inverse()?;
            // t[1].Mul(&t[1], &t[2])
            y1 *= &y2;
            // t[2].Expt(&t[1])
            Self::exp_by_x(&y1, &mut y2);
            // t[1].InverseUnitary(&t[1])
            y1.cyclotomic_inverse_in_place();
            // t[1].Mul(&t[1], &t[2])
            y1 *= &y2;
            // t[2].Expt(&t[1])
            Self::exp_by_x(&y1, &mut y2);
            // t[1].Frobenius(&t[1])
            y1.frobenius_map(1);
            // t[1].Mul(&t[1], &t[2])
            y1 *= &y2;
            // result.Mul(&result, &t[0])
            r *= &y0;
            // t[0].Expt(&t[1])
            Self::exp_by_x(&y1, &mut y0);
            // t[2].Expt(&t[0])
            Self::exp_by_x(&y0, &mut y2);
            // t[0].FrobeniusSquare(&t[1])
            y0 = y1;
            y0.frobenius_map(2);
            // t[1].InverseUnitary(&t[1])
            y1.cyclotomic_inverse_in_place();
            // t[1].Mul(&t[1], &t[2])
            y1 *= &y2;
            // t[1].Mul(&t[1], &t[0])
            y1 *= &y0;
            // result.Mul(&result, &t[1])
            r *= &y1;
            Some(PairingOutput(r))
        })
    }
}
