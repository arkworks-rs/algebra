use crate::{
    models::{ModelParameters, SWModelParameters},
    PairingEngine,
};
use ark_ff::fields::{
    fp12_2over3over2::{Fp12, Fp12Parameters},
    fp2::Fp2Parameters,
    fp6_3over2::Fp6Parameters,
    BitIteratorBE, Field, Fp2, PrimeField, SquareRootField,
};
use num_traits::One;

use core::marker::PhantomData;

pub enum TwistType {
    M,
    D,
}

pub trait Bls12Parameters: 'static {
    const X: &'static [u64];
    const X_IS_NEGATIVE: bool;
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
                c2.mul_assign_by_fp(&p.y);
                c1.mul_assign_by_fp(&p.x);
                f.mul_by_014(&c0, &c1, &c2);
            }
            TwistType::D => {
                c0.mul_assign_by_fp(&p.y);
                c1.mul_assign_by_fp(&p.x);
                f.mul_by_034(&c0, &c1, &c2);
            }
        }
    }

    fn exp_by_x(mut f: Fp12<P::Fp12Params>) -> Fp12<P::Fp12Params> {
        f = f.cyclotomic_exp(P::X);
        if P::X_IS_NEGATIVE {
            f.conjugate();
        }
        f
    }
}

impl<P: Bls12Parameters> PairingEngine for Bls12<P> {
    type Fr = <P::G1Parameters as ModelParameters>::ScalarField;
    type G1Projective = G1Projective<P>;
    type G1Affine = G1Affine<P>;
    type G1Prepared = G1Prepared<P>;
    type G2Projective = G2Projective<P>;
    type G2Affine = G2Affine<P>;
    type G2Prepared = G2Prepared<P>;
    type Fq = P::Fp;
    type Fqe = Fp2<P::Fp2Params>;
    type Fqk = Fp12<P::Fp12Params>;

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

        for i in BitIteratorBE::new(P::X).skip(1) {
            f.square_in_place();

            for (p, ref mut coeffs) in &mut pairs {
                Self::ell(&mut f, coeffs.next().unwrap(), &p.0);
            }

            if i {
                for &mut (p, ref mut coeffs) in &mut pairs {
                    Self::ell(&mut f, coeffs.next().unwrap(), &p.0);
                }
            }
        }

        if P::X_IS_NEGATIVE {
            f.conjugate();
        }

        f
    }

    fn final_exponentiation(f: &Self::Fqk) -> Option<Self::Fqk> {
        // Computing the final exponentation following
        // https://eprint.iacr.org/2020/875 
        // Adapted from the implementation in https://github.com/ConsenSys/gurvy/pull/29

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

            // Hard part of the final exponentation:
            // t[0].CyclotomicSquare(&result)
            let mut y0 = r.cyclotomic_square();
            // t[1].Expt(&result)
            let mut y1 = Self::exp_by_x(r);
            // t[2].InverseUnitary(&result)
            let mut y2 = r;
            y2.conjugate();
            // t[1].Mul(&t[1], &t[2])
            y1 *= y2;
            // t[2].Expt(&t[1])
            y2 = Self::exp_by_x(y1);
            // t[1].InverseUnitary(&t[1])
            y1.conjugate();
            // t[1].Mul(&t[1], &t[2])
            y1 *= y2;
            // t[2].Expt(&t[1])
            y2 = Self::exp_by_x(y1);
            // t[1].Frobenius(&t[1])
            y1.frobenius_map(1);
            // t[1].Mul(&t[1], &t[2])
            y1 *= &y2;
            // result.Mul(&result, &t[0])
            r *= y0;
            // t[0].Expt(&t[1])
            y0 = Self::exp_by_x(y1);
            // t[2].Expt(&t[0])
            y2 = Self::exp_by_x(y0);
            // t[0].FrobeniusSquare(&t[1])
            y0 = y1;
            y0.frobenius_map(2);
            // t[1].InverseUnitary(&t[1])
            y1.conjugate();
            // t[1].Mul(&t[1], &t[2])
            y1 *= y2;
            // t[1].Mul(&t[1], &t[0])
            y1 *= y0;
            // result.Mul(&result, &t[1])
            r *= y1;
            r
        })
    }
}
