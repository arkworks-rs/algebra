use crate::{
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
    pairing::{MillerLoopOutput, Pairing, PairingOutput},
};
use ark_ff::{
    fp3::{Fp3, Fp3Config},
    fp6_2over3::{Fp6, Fp6Config},
    AdditiveGroup, CyclotomicMultSubgroup, Field, PrimeField,
};
use educe::Educe;
use itertools::Itertools;
use num_traits::{One, Zero};

use ark_std::{marker::PhantomData, vec::*};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub mod g1;
pub mod g2;

use self::g2::{AteAdditionCoefficients, AteDoubleCoefficients, G2ProjectiveExtended};
pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};

pub type GT<P> = Fp6<P>;

pub trait MNT6Config: 'static + Sized {
    const TWIST: Fp3<Self::Fp3Config>;
    const TWIST_COEFF_A: Fp3<Self::Fp3Config>;
    const ATE_LOOP_COUNT: &'static [i8];
    const ATE_IS_LOOP_COUNT_NEG: bool;
    const FINAL_EXPONENT_LAST_CHUNK_1: <Self::Fp as PrimeField>::BigInt;
    const FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG: bool;
    const FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0: <Self::Fp as PrimeField>::BigInt;
    type Fp: PrimeField + Into<<Self::Fp as PrimeField>::BigInt>;
    type Fr: PrimeField + Into<<Self::Fr as PrimeField>::BigInt>;
    type Fp3Config: Fp3Config<Fp = Self::Fp>;
    type Fp6Config: Fp6Config<Fp3Config = Self::Fp3Config>;
    type G1Config: SWCurveConfig<BaseField = Self::Fp, ScalarField = Self::Fr>;
    type G2Config: SWCurveConfig<
        BaseField = Fp3<Self::Fp3Config>,
        ScalarField = <Self::G1Config as CurveConfig>::ScalarField,
    >;

    fn multi_miller_loop(
        a: impl IntoIterator<Item = impl Into<G1Prepared<Self>>>,
        b: impl IntoIterator<Item = impl Into<G2Prepared<Self>>>,
    ) -> MillerLoopOutput<MNT6<Self>> {
        let pairs = a
            .into_iter()
            .zip_eq(b)
            .map(|(a, b)| (a.into(), b.into()))
            .collect::<Vec<_>>();
        let result = ark_std::cfg_into_iter!(pairs)
            .map(|(a, b)| MNT6::<Self>::ate_miller_loop(&a, &b))
            .product();
        MillerLoopOutput(result)
    }

    fn final_exponentiation(f: MillerLoopOutput<MNT6<Self>>) -> Option<PairingOutput<MNT6<Self>>> {
        let value = f.0;
        let value_inv = value.inverse()?;
        let value_to_first_chunk =
            MNT6::<Self>::final_exponentiation_first_chunk(&value, &value_inv);
        let value_inv_to_first_chunk =
            MNT6::<Self>::final_exponentiation_first_chunk(&value_inv, &value);
        let result = MNT6::<Self>::final_exponentiation_last_chunk(
            &value_to_first_chunk,
            &value_inv_to_first_chunk,
        );
        Some(PairingOutput(result))
    }
}

#[derive(Educe)]
#[educe(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct MNT6<P: MNT6Config>(PhantomData<fn() -> P>);

impl<P: MNT6Config> MNT6<P> {
    fn doubling_for_flipped_miller_loop(
        r: &G2ProjectiveExtended<P>,
    ) -> (G2ProjectiveExtended<P>, AteDoubleCoefficients<P>) {
        let a = r.t.square();
        let b = r.x.square();
        let c = r.y.square();
        let d = c.square();
        let e = (r.x + &c).square() - &b - &d;
        let f = (b + &b + &b) + &(P::TWIST_COEFF_A * &a);
        let g = f.square();

        let d_eight = d.double().double().double();

        let e2 = e.double();
        let x = g - &e2.double();
        let y = -d_eight + &(f * &(e2 - &x));
        let z = (r.y + &r.z).square() - &c - &r.z.square();
        let t = z.square();

        let r2 = G2ProjectiveExtended { x, y, z, t };
        let coeff = AteDoubleCoefficients {
            c_h: (r2.z + &r.t).square() - &r2.t - &a,
            c_4c: c + &c + &c + &c,
            c_j: (f + &r.t).square() - &g - &a,
            c_l: (f + &r.x).square() - &g - &b,
        };

        (r2, coeff)
    }

    fn mixed_addition_for_flipper_miller_loop(
        x: &Fp3<P::Fp3Config>,
        y: &Fp3<P::Fp3Config>,
        r: &G2ProjectiveExtended<P>,
    ) -> (G2ProjectiveExtended<P>, AteAdditionCoefficients<P>) {
        let a = y.square();
        let b = r.t * x;
        let d = ((r.z + y).square() - &a - &r.t) * &r.t;
        let h = b - &r.x;
        let i = h.square();
        let e = i + &i + &i + &i;
        let j = h * &e;
        let v = r.x * &e;
        let ry2 = r.y.double();
        let l1 = d - &ry2;

        let x = l1.square() - &j - &(v + &v);
        let y = l1 * &(v - &x) - &(j * &ry2);
        let z = (r.z + &h).square() - &r.t - &i;
        let t = z.square();

        let r2 = G2ProjectiveExtended { x, y, z, t };
        let coeff = AteAdditionCoefficients { c_l1: l1, c_rz: z };

        (r2, coeff)
    }

    pub fn ate_miller_loop(p: &G1Prepared<P>, q: &G2Prepared<P>) -> Fp6<P::Fp6Config> {
        let l1_coeff = Fp3::new(p.x, P::Fp::zero(), P::Fp::zero()) - &q.x_over_twist;

        let mut f = <Fp6<P::Fp6Config>>::one();

        let mut add_idx: usize = 0;

        // code below gets executed for all bits (EXCEPT the MSB itself) of
        // mnt6_param_p (skipping leading zeros) in MSB to LSB order
        let y_over_twist_neg = -q.y_over_twist;
        assert_eq!(P::ATE_LOOP_COUNT.len() - 1, q.double_coefficients.len());
        for (bit, dc) in P::ATE_LOOP_COUNT.iter().skip(1).zip(&q.double_coefficients) {
            let g_rr_at_p = Fp6::new(
                dc.c_l - &dc.c_4c - &(dc.c_j * &p.x_twist),
                dc.c_h * &p.y_twist,
            );

            f = f.square() * &g_rr_at_p;

            // Compute l_{R,Q}(P) if bit == 1, and l_{R,-Q}(P) if bit == -1
            let g_rq_at_p = if *bit == 1 {
                let ac = &q.addition_coefficients[add_idx];
                add_idx += 1;

                Fp6::new(
                    ac.c_rz * &p.y_twist,
                    -(q.y_over_twist * &ac.c_rz + &(l1_coeff * &ac.c_l1)),
                )
            } else if *bit == -1 {
                let ac = &q.addition_coefficients[add_idx];
                add_idx += 1;
                Fp6::new(
                    ac.c_rz * &p.y_twist,
                    -(y_over_twist_neg * &ac.c_rz + &(l1_coeff * &ac.c_l1)),
                )
            } else if *bit == 0 {
                continue;
            } else {
                unreachable!();
            };
            f *= &g_rq_at_p;
        }

        if P::ATE_IS_LOOP_COUNT_NEG {
            let ac = &q.addition_coefficients[add_idx];

            let g_rnegr_at_p = Fp6::new(
                ac.c_rz * &p.y_twist,
                -(q.y_over_twist * &ac.c_rz + &(l1_coeff * &ac.c_l1)),
            );
            f = (f * &g_rnegr_at_p).inverse().unwrap();
        }

        f
    }

    fn final_exponentiation_first_chunk(
        elt: &Fp6<P::Fp6Config>,
        elt_inv: &Fp6<P::Fp6Config>,
    ) -> Fp6<P::Fp6Config> {
        // (q^3-1)*(q+1)

        // elt_q3 = elt^(q^3)
        let mut elt_q3 = *elt;
        elt_q3.cyclotomic_inverse_in_place();
        // elt_q3_over_elt = elt^(q^3-1)
        let elt_q3_over_elt = elt_q3 * elt_inv;
        // alpha = elt^((q^3-1) * q)
        let mut alpha = elt_q3_over_elt;
        alpha.frobenius_map_in_place(1);
        // beta = elt^((q^3-1)*(q+1)
        alpha * &elt_q3_over_elt
    }

    fn final_exponentiation_last_chunk(
        elt: &Fp6<P::Fp6Config>,
        elt_inv: &Fp6<P::Fp6Config>,
    ) -> Fp6<P::Fp6Config> {
        let elt_clone = *elt;
        let elt_inv_clone = *elt_inv;

        let mut elt_q = *elt;
        elt_q.frobenius_map_in_place(1);

        let w1_part = elt_q.cyclotomic_exp(P::FINAL_EXPONENT_LAST_CHUNK_1);
        let w0_part = if P::FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG {
            elt_inv_clone.cyclotomic_exp(P::FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0)
        } else {
            elt_clone.cyclotomic_exp(P::FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0)
        };

        w1_part * &w0_part
    }
}

impl<P: MNT6Config> Pairing for MNT6<P> {
    type BaseField = <P::G1Config as CurveConfig>::BaseField;
    type ScalarField = <P::G1Config as CurveConfig>::ScalarField;
    type G1 = G1Projective<P>;
    type G1Affine = G1Affine<P>;
    type G1Prepared = G1Prepared<P>;
    type G2 = G2Projective<P>;
    type G2Affine = G2Affine<P>;
    type G2Prepared = G2Prepared<P>;
    type TargetField = Fp6<P::Fp6Config>;

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
