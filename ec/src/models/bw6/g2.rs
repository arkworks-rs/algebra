use ark_ff::{AdditiveGroup, BitIteratorBE, Field};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::*;
use educe::Educe;
use num_traits::One;

use crate::{
    bw6::{BW6Config, TwistType},
    models::short_weierstrass::SWCurveConfig,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};

pub type G2Affine<P> = Affine<<P as BW6Config>::G2Config>;
pub type G2Projective<P> = Projective<<P as BW6Config>::G2Config>;

#[derive(Educe, CanonicalSerialize, CanonicalDeserialize)]
#[educe(Clone, Debug, PartialEq, Eq)]
pub struct G2Prepared<P: BW6Config> {
    /// Stores the coefficients of the line evaluations as calculated in
    /// <https://eprint.iacr.org/2013/722.pdf>
    pub ell_coeffs_1: Vec<(P::Fp, P::Fp, P::Fp)>,
    pub ell_coeffs_2: Vec<(P::Fp, P::Fp, P::Fp)>,
    pub infinity: bool,
}

#[derive(Educe, CanonicalSerialize, CanonicalDeserialize)]
#[educe(Clone, Copy, Debug)]
pub struct G2HomProjective<P: BW6Config> {
    x: P::Fp,
    y: P::Fp,
    z: P::Fp,
}

impl<P: BW6Config> Default for G2Prepared<P> {
    fn default() -> Self {
        Self::from(G2Affine::<P>::generator())
    }
}

// impl into G2Affine from G2HomProjective
impl<P: BW6Config> From<G2HomProjective<P>> for G2Affine<P> {
    fn from(q: G2HomProjective<P>) -> Self {
        let z_inv = q.z.inverse().unwrap();
        let x = q.x * &z_inv;
        let y = q.y * &z_inv;
        G2Affine::<P>::new_unchecked(x, y)
    }
}

impl<P: BW6Config> From<G2Affine<P>> for G2Prepared<P> {
    fn from(q: G2Affine<P>) -> Self {
        if q.infinity {
            return Self {
                ell_coeffs_1: vec![],
                ell_coeffs_2: vec![],
                infinity: true,
            };
        }

        // f_{u,Q}(P)
        let mut ell_coeffs_1 = vec![];
        let mut r = G2HomProjective::<P> {
            x: q.x,
            y: q.y,
            z: P::Fp::one(),
        };

        for i in BitIteratorBE::new(P::ATE_LOOP_COUNT_1).skip(1) {
            ell_coeffs_1.push(r.double_in_place());

            if i {
                ell_coeffs_1.push(r.add_in_place(&q));
            }
        }
        // TODO: this is probably the slowest part
        // While G2 preparation is overall faster due to shortened 2nd loop,
        // The inversion could probably be avoided by using Hom(P) + Hom(Q) addition,
        // instead of mixed addition as is currently done.
        let r_affine: G2Affine<P> = r.into();
        // Swap the signs of `qu`, `r` & `neg_qu` if the loop count is negative.
        let (qu, neg_qu) = if P::ATE_LOOP_COUNT_1_IS_NEGATIVE {
            (-r_affine, r_affine)
        } else {
            (r_affine, -r_affine)
        };

        r = G2HomProjective::<P> {
            x: qu.x,
            y: qu.y,
            z: P::Fp::one(),
        };
        ell_coeffs_1.push(r.clone().add_in_place(&q));

        let mut ell_coeffs_2 = vec![];

        // f_{u^2-u-1,[u]Q}(P)
        for bit in P::ATE_LOOP_COUNT_2.iter().rev().skip(1) {
            ell_coeffs_2.push(r.double_in_place());

            match bit {
                1 => ell_coeffs_2.push(r.add_in_place(&qu)),
                -1 => ell_coeffs_2.push(r.add_in_place(&neg_qu)),
                _ => continue,
            }
        }

        Self {
            ell_coeffs_1,
            ell_coeffs_2,
            infinity: false,
        }
    }
}

impl<'a, P: BW6Config> From<&'a G2Affine<P>> for G2Prepared<P> {
    fn from(q: &'a G2Affine<P>) -> Self {
        (*q).into()
    }
}

impl<'a, P: BW6Config> From<&'a G2Projective<P>> for G2Prepared<P> {
    fn from(q: &'a G2Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: BW6Config> From<G2Projective<P>> for G2Prepared<P> {
    fn from(q: G2Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: BW6Config> G2Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.infinity
    }
}

impl<P: BW6Config> G2HomProjective<P> {
    pub fn double_in_place(&mut self) -> (P::Fp, P::Fp, P::Fp) {
        // Formula for line function when working with
        // homogeneous projective coordinates, as described in
        // <https://eprint.iacr.org/2013/722.pdf>.

        let a = self.x * &self.y;
        let b = self.y.square();
        let b4 = b.double().double();
        let c = self.z.square();
        let e = P::G2Config::COEFF_B * &(c.double() + &c);
        let f = e.double() + &e;
        let g = b + &f;
        let h = (self.y + &self.z).square() - &(b + &c);
        let i = e - &b;
        let j = self.x.square();
        let e2_square = e.double().square();

        self.x = a.double() * &(b - &f);
        self.y = g.square() - &(e2_square.double() + &e2_square);
        self.z = b4 * &h;
        match P::TWIST_TYPE {
            TwistType::M => (i, j.double() + &j, -h),
            TwistType::D => (-h, j.double() + &j, i),
        }
    }

    pub fn add_in_place(&mut self, q: &G2Affine<P>) -> (P::Fp, P::Fp, P::Fp) {
        // Formula for line function when working with
        // homogeneous projective coordinates, as described in https://eprint.iacr.org/2013/722.pdf.
        let theta = self.y - &(q.y * &self.z);
        let lambda = self.x - &(q.x * &self.z);
        let c = theta.square();
        let d = lambda.square();
        let e = lambda * &d;
        let f = self.z * &c;
        let g = self.x * &d;
        let h = e + &f - &g.double();
        self.x = lambda * &h;
        self.y = theta * &(g - &h) - &(e * &self.y);
        self.z *= &e;
        let j = theta * &q.x - &(lambda * &q.y);

        match P::TWIST_TYPE {
            TwistType::M => (j, -theta, lambda),
            TwistType::D => (lambda, -theta, j),
        }
    }
}
