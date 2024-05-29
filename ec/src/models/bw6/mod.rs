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
use ark_std::cfg_chunks_mut;
use educe::Educe;
use itertools::Itertools;
use num_traits::One;

use ark_std::{marker::PhantomData, vec::*};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub enum TwistType {
    M,
    D,
}

pub trait BW6Config: 'static + Eq + Sized {
    const X: <Self::Fp as PrimeField>::BigInt;
    const X_IS_NEGATIVE: bool;
    // [X-1]/3 for X>0, and [(-X)+1]/3 otherwise
    const X_MINUS_1_DIV_3: <Self::Fp as PrimeField>::BigInt;
    const ATE_LOOP_COUNT_1: &'static [u64];
    const ATE_LOOP_COUNT_1_IS_NEGATIVE: bool;
    // X^2 - X - 1
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

    // Computes the exponent of an element of the cyclotomic subgroup,
    // and inverses the result if necessary.
    fn cyclotomic_exp_signed(
        f: &Fp6<Self::Fp6Config>,
        x: impl AsRef<[u64]>,
        invert: bool,
    ) -> Fp6<Self::Fp6Config> {
        let mut f = f.cyclotomic_exp(x);
        if invert {
            f.cyclotomic_inverse_in_place();
        }
        f
    }

    // Computes the exponent of an element of the cyclotomic subgroup by the curve seed
    fn exp_by_x(f: &Fp6<Self::Fp6Config>) -> Fp6<Self::Fp6Config> {
        Self::cyclotomic_exp_signed(f, &Self::X, Self::X_IS_NEGATIVE)
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

        // compute f_u which we can later re-use for the 2nd loop
        let mut f_u = cfg_chunks_mut!(pairs_1, 4)
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

        let f_u_inv;

        if Self::ATE_LOOP_COUNT_1_IS_NEGATIVE {
            f_u_inv = f_u;
            f_u.cyclotomic_inverse_in_place();
        } else {
            f_u_inv = f_u.cyclotomic_inverse().unwrap();
        }

        // f_1(P) = f_(u+1)(P) = f_u(P) * l([u]q, q)(P)
        let mut f_1 = cfg_chunks_mut!(pairs_1, 4)
            .map(|pairs| {
                pairs.iter_mut().fold(f_u, |mut f, (p, coeffs)| {
                    BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                    f
                })
            })
            .product::<<BW6<Self> as Pairing>::TargetField>();

        let mut f_2 = cfg_chunks_mut!(pairs_2, 4)
            .map(|pairs| {
                let mut f = f_u;
                for i in (1..Self::ATE_LOOP_COUNT_2.len()).rev() {
                    f.square_in_place();

                    for (p, ref mut coeffs) in pairs.iter_mut() {
                        BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                    }

                    let bit = Self::ATE_LOOP_COUNT_2[i - 1];
                    if bit == 1 {
                        f *= &f_u;
                    } else if bit == -1 {
                        f *= &f_u_inv;
                    } else {
                        continue;
                    }
                    for &mut (p, ref mut coeffs) in pairs.iter_mut() {
                        BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
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

#[derive(Educe)]
#[educe(Copy, Clone, PartialEq, Eq, Debug, Hash)]
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
        P::cyclotomic_exp_signed(f, &P::X_MINUS_1_DIV_3, P::X_IS_NEGATIVE)
    }

    // f^[(p^3-1)(p+1)]
    fn final_exponentiation_easy_part(f: Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
        // f^(-1)
        let f_inv = f.inverse().unwrap();
        // f^(p^3)
        let f_p3 = {
            let mut f = f;
            f.conjugate_in_place();
            f
        };
        // g := f^(p^3-1) = f^(p^3) * f^(-1)
        let g = f_p3 * f_inv;
        // g^p
        let g_p = {
            let mut g = g;
            g.frobenius_map_in_place(1);
            g
        };
        // g^(p+1) = g^p * g
        g_p * &g
    }

    fn final_exponentiation_hard_part(f: &Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
        // Generic implementation of the hard part of the final exponentiation for the BW6 family.
        // Computes (u+1)*Phi_k(p(u))/r(u)
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
            let f = (Self::exp_by_x_plus_1(&e) * &c)
                .cyclotomic_inverse()
                .unwrap()
                * &d;
            // G = ((F * D)**(u+1)).conjugate() * C * B
            let g = Self::exp_by_x_plus_1(&(f * &d))
                .cyclotomic_inverse()
                .unwrap()
                * &c
                * &b;
            // d2 = (ht**2+3*hy**2)//4
            let d2 = ((P::H_T * P::H_T + 3 * P::H_Y * P::H_Y) / 4) as u64;
            // d1 = (ht-hy)//2
            let d1 = (P::H_T - P::H_Y) / 2;
            // H = F**d1 * E
            let h = P::cyclotomic_exp_signed(&f, &[d1 as u64], d1 < 0) * &e;
            // H = H**2 * H * B * G**d2
            let h = h.square() * &h * &b * g.cyclotomic_exp(&[d2]);
            // return A * H
            a * &h
        } else {
            // Algorithm 4.4 from https://yelhousni.github.io/phd.pdf
            // Follows the implementation https://gitlab.inria.fr/zk-curves/snark-2-chains/-/blob/master/sage/pairing_bw6_bls12.py#L969

            // A = m**(u-1)
            let a = Self::exp_by_x_minus_1(f);
            // A = A**(u-1)
            let a = Self::exp_by_x_minus_1(&a);
            // A = A * m.frobenius()
            let a = a * f.frobenius_map(1);
            // B = A**(u+1) * m.conjugate()
            let b = Self::exp_by_x_plus_1(&a) * f.cyclotomic_inverse().unwrap();
            // A = A**2 * A
            let a = a.square() * &a;
            // C = B**((u-1)//3)
            let c = Self::exp_by_x_minus_1_div_3(&b);
            // D = C**(u-1)
            let d = Self::exp_by_x_minus_1(&c);
            // E = (D**(u-1))**(u-1) * D
            let e = Self::exp_by_x_minus_1(&Self::exp_by_x_minus_1(&d)) * &d;
            // D = D.conjugate()
            let d = d.cyclotomic_inverse().unwrap();
            // Fc = D * B
            let fc = d * &b;
            // G = E**(u+1) * Fc
            let g = Self::exp_by_x_plus_1(&e) * &fc;
            // H = G * C
            let h = g * &c;
            // I = (G * D)**(u+1) * Fc.conjugate()
            let i = Self::exp_by_x_plus_1(&(g * &d)) * fc.cyclotomic_inverse().unwrap();
            // d2 = (ht**2+3*hy**2)//4
            let d2 = ((P::H_T * P::H_T + 3 * P::H_Y * P::H_Y) / 4) as u64;
            // d1 = (ht+hy)//2
            let d1 = (P::H_T + P::H_Y) / 2;
            // J = H**d1 * E
            let j = P::cyclotomic_exp_signed(&h, &[d1 as u64], d1 < 0) * &e;
            // K = J**2 * J * B * I**d2
            let k = j.square() * &j * &b * i.cyclotomic_exp(&[d2]);
            // return A * K
            a * &k
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
