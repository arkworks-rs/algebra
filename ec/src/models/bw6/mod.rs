use crate::{
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
    pairing::{MillerLoopOutput, Pairing, PairingOutput},
};
use ark_ff::{
    fields::{
        fp3::Fp3Config,
        fp6_2over3::{Fp6, Fp6Config},
        Field, PrimeField,
    },
    BitIteratorBE, CyclotomicMultSubgroup,
};
use itertools::Itertools;
use num_traits::One;

use ark_std::{marker::PhantomData, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub enum TwistType {
    M,
    D,
}

pub trait BW6Config: 'static + Eq + Sized {
    const X: <Self::Fp as PrimeField>::BigInt;
    const X_IS_NEGATIVE: bool;
    const ATE_LOOP_COUNT_1: &'static [u64];
    const ATE_LOOP_COUNT_1_IS_NEGATIVE: bool;
    const ATE_LOOP_COUNT_2: &'static [i8];
    const ATE_LOOP_COUNT_2_IS_NEGATIVE: bool;
    const TWIST_TYPE: TwistType;
    const H_T: i64;
    const H_Y: i64;
    const T_MOD_R_IS_ZERO: bool;
    type Fp: PrimeField + Into<<Self::Fp as PrimeField>::BigInt>;
    type Fp3Config: Fp3Config<Fp = Self::Fp>;
    type Fp6Config: Fp6Config<Fp3Config = Self::Fp3Config>;
    type G1Config: SWCurveConfig<BaseField = Self::Fp>;
    type G2Config: SWCurveConfig<
        BaseField = Self::Fp,
        ScalarField = <Self::G1Config as CurveConfig>::ScalarField,
    >;

    fn exp_by_x(f: &Fp6<Self::Fp6Config>) -> Fp6<Self::Fp6Config> {
        let mut f = f.cyclotomic_exp(&Self::X);
        if Self::X_IS_NEGATIVE {
            f.cyclotomic_inverse_in_place();
        }
        f
    }

    fn final_exponentiation_hard_part(f: &Fp6<Self::Fp6Config>) -> Fp6<Self::Fp6Config> {
        BW6::<Self>::final_exponentiation_hard_part(f)
    }

    fn final_exponentiation(f: MillerLoopOutput<BW6<Self>>) -> Option<PairingOutput<BW6<Self>>> {
        let easy_part = BW6::<Self>::final_exponentiation_easy_part(f.0);
        Some(Self::final_exponentiation_hard_part(&easy_part)).map(PairingOutput)
    }

    fn multi_miller_loop(
        a: impl IntoIterator<Item = impl Into<G1Prepared<Self>>>,
        b: impl IntoIterator<Item = impl Into<G2Prepared<Self>>>,
    ) -> MillerLoopOutput<BW6<Self>> {
        // Implements unoptimized version of the Miller loop for the optimal ate pairing.
        // See formulas (4.15) and (4.17) from https://yelhousni.github.io/phd.pdf

        let (mut pairs_1, mut pairs_2) = a
            .into_iter()
            .zip_eq(b)
            .filter_map(|(p, q)| {
                let (p, q): (G1Prepared<Self>, G2Prepared<Self>) = (p.into(), q.into());
                match !p.is_zero() && !q.is_zero() {
                    true => Some((
                        (p, q.ell_coeffs_1.into_iter()),
                        (p, q.ell_coeffs_2.into_iter()),
                    )),
                    false => None,
                }
            })
            .unzip::<_, _, Vec<_>, Vec<_>>();

        let mut f_1 = cfg_chunks_mut!(pairs_1, 4)
            .map(|pairs| {
                let mut f = <BW6<Self> as Pairing>::TargetField::one();
                for i in BitIteratorBE::without_leading_zeros(Self::ATE_LOOP_COUNT_1).skip(1) {
                    f.square_in_place();
                    for (p, coeffs) in pairs.iter_mut() {
                        BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                    }
                    if i {
                        for (p, coeffs) in pairs.iter_mut() {
                            BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                        }
                    }
                }
                f
            })
            .product::<<BW6<Self> as Pairing>::TargetField>();

        if Self::ATE_LOOP_COUNT_1_IS_NEGATIVE {
            f_1.cyclotomic_inverse_in_place();
        }
        let mut f_2 = cfg_chunks_mut!(pairs_2, 4)
            .map(|pairs| {
                let mut f = <<BW6<Self> as Pairing>::TargetField>::one();
                for i in (1..Self::ATE_LOOP_COUNT_2.len()).rev() {
                    if i != Self::ATE_LOOP_COUNT_2.len() - 1 {
                        f.square_in_place();
                    }

                    for (p, ref mut coeffs) in pairs.iter_mut() {
                        BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                    }

                    let bit = Self::ATE_LOOP_COUNT_2[i - 1];
                    if bit == 1 || bit == -1 {
                        for &mut (p, ref mut coeffs) in pairs.iter_mut() {
                            BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                        }
                    }
                }
                f
            })
            .product::<<BW6<Self> as Pairing>::TargetField>();

        if Self::ATE_LOOP_COUNT_2_IS_NEGATIVE {
            f_2.cyclotomic_inverse_in_place();
        }

        if Self::T_MOD_R_IS_ZERO {
            f_1.frobenius_map_in_place(1);
        } else {
            f_2.frobenius_map_in_place(1);
        }

        MillerLoopOutput(f_1 * &f_2)
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
pub struct BW6<P: BW6Config>(PhantomData<fn() -> P>);

impl<P: BW6Config> BW6<P> {
    // Evaluate the line function at point p.
    fn ell(f: &mut Fp6<P::Fp6Config>, coeffs: &(P::Fp, P::Fp, P::Fp), p: &G1Affine<P>) {
        let mut c0 = coeffs.0;
        let mut c1 = coeffs.1;
        let mut c2 = coeffs.2;

        match P::TWIST_TYPE {
            TwistType::M => {
                c2 *= &p.y;
                c1 *= &p.x;
                f.mul_by_014(&c0, &c1, &c2);
            },
            TwistType::D => {
                c0 *= &p.y;
                c1 *= &p.x;
                f.mul_by_034(&c0, &c1, &c2);
            },
        }
    }

    fn exp_by_x_plus_1(f: &Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
        P::exp_by_x(f) * f
    }

    fn exp_by_x_minus_1(f: &Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
        P::exp_by_x(f) * &f.cyclotomic_inverse().unwrap()
    }

    fn exp_by_x_minus_1_div_3(f: &Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
        let u = P::Fp::from(P::X);
        let one = P::Fp::one();
        let three = P::Fp::from(3u32);
        if P::X_IS_NEGATIVE {
            let exp = (u + one) / three;
            f.cyclotomic_exp(exp.into_bigint()).cyclotomic_inverse().unwrap()
        } else {
            let exp = (u - one) / three;
            f.cyclotomic_exp(exp.into_bigint())
        }
    }

    fn final_exponentiation_easy_part(
        elt: Fp6<P::Fp6Config>
    ) -> Fp6<P::Fp6Config> {
        // (q^3-1)*(q+1)
        let elt_inv = elt.inverse().unwrap();
        // elt_q3 = elt^(q^3)
        let mut elt_q3 = elt;
        elt_q3.cyclotomic_inverse_in_place();
        // elt_q3_over_elt = elt^(q^3-1)
        let elt_q3_over_elt = elt_q3 * elt_inv;
        // alpha = elt^((q^3-1) * q)
        let mut alpha = elt_q3_over_elt;
        alpha.frobenius_map_in_place(1);
        // beta = elt^((q^3-1)*(q+1)
        alpha * &elt_q3_over_elt
    }

    fn final_exponentiation_hard_part(f: &Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
        // Generic implementation of the hard part of the final exponentiation for the BW6 family.
        if P::T_MOD_R_IS_ZERO {
            // Algorithm 4.3 from https://yelhousni.github.io/phd.pdf
            // Follows the implementation https://gitlab.inria.fr/zk-curves/snark-2-chains/-/blob/master/sage/pairing_bw6_bls12.py#L1036

            // A = m**(u-1)
            let a = Self::exp_by_x_minus_1(f);
            // A = A**(u-1)
            let a = Self::exp_by_x_minus_1(&a);
            // A = (m * A).conjugate() * m.frobenius()
            let a = (f * &a).cyclotomic_inverse().unwrap() * f.frobenius_map(1);
            // B = A**(u+1) * m
            let b = Self::exp_by_x_plus_1(&a) * f;
            // A = A**2 * A
            let a = a.square() * &a;
            // A = A.conjugate()
            let a = a.cyclotomic_inverse().unwrap();
            // C = B**((u-1)//3)
            let c = Self::exp_by_x_minus_1_div_3(&b);
            // D = C**(u-1)
            let d = Self::exp_by_x_minus_1(&c);
            // E = (D**(u-1))**(u-1) * D
            let e = Self::exp_by_x_minus_1(&Self::exp_by_x_minus_1(&d)) * &d;
            // F = (E**(u+1) * C).conjugate() * D
            let f = (Self::exp_by_x_plus_1(&e) * &c).cyclotomic_inverse().unwrap() * &d;
            // G = ((F * D)**(u+1)).conjugate() * C * B
            let g = Self::exp_by_x_plus_1(&(f * &d)).cyclotomic_inverse().unwrap() * &c * &b;
            // d2 = (ht**2+3*hy**2)//4
            let d2 = ((P::H_T * P::H_T + 3 * P::H_Y * P::H_Y) / 4) as u32;
            let d2 = <P::Fp as PrimeField>::BigInt::from(d2);
            // d1 = (ht-hy)//2
            let d1 = ((P::H_T - P::H_Y) / 2) as u32;
            let d1 = <P::Fp as PrimeField>::BigInt::from(d1);
            // H = F**d1 * E
            let h = f.cyclotomic_exp(d1) * &e;
            // H = H**2 * H * B * G**d2
            let h = h.square() * &h * &b * g.cyclotomic_exp(d2);
            // return A * H
            a * &h
        } else {
            unimplemented!()
        }
    }
}

impl<P: BW6Config> Pairing for BW6<P> {
    type BaseField = <P::G1Config as CurveConfig>::BaseField;
    type ScalarField = <P::G1Config as CurveConfig>::ScalarField;
    type G1 = G1Projective<P>;
    type G1Affine = G1Affine<P>;
    type G1Prepared = G1Prepared<P>;
    type G2 = G2Projective<P>;
    type G2Affine = G2Affine<P>;
    type G2Prepared = G2Prepared<P>;
    type TargetField = Fp6<P::Fp6Config>;

    fn final_exponentiation(f: MillerLoopOutput<Self>) -> Option<PairingOutput<Self>> {
        P::final_exponentiation(f)
    }

    fn multi_miller_loop(
        a: impl IntoIterator<Item = impl Into<Self::G1Prepared>>,
        b: impl IntoIterator<Item = impl Into<Self::G2Prepared>>,
    ) -> MillerLoopOutput<Self> {
        P::multi_miller_loop(a, b)
    }
}
