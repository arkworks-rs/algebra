use ark_ff::{
    fields::{BitIteratorBE, Field, Fp2},
    Zero,
};
use ark_std::{vec::Vec, One};

use crate::{
    bls12::{Bls12Parameters, TwistType},
    models::short_weierstrass::SWCurveConfig,
    short_weierstrass::{Affine, Projective},
    AffineCurve,
};

pub type G2Affine<P> = Affine<<P as Bls12Parameters>::G2Parameters>;
pub type G2Projective<P> = Projective<<P as Bls12Parameters>::G2Parameters>;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "P: Bls12Parameters"),
    Debug(bound = "P: Bls12Parameters"),
    PartialEq(bound = "P: Bls12Parameters"),
    Eq(bound = "P: Bls12Parameters")
)]
pub struct G2Prepared<P: Bls12Parameters> {
    // Stores the coefficients of the line evaluations as calculated in
    // https://eprint.iacr.org/2013/722.pdf
    pub ell_coeffs: Vec<EllCoeff<Fp2<P::Fp2Config>>>,
    pub infinity: bool,
}

pub(crate) type EllCoeff<F> = (F, F, F);

#[derive(Derivative)]
#[derivative(
    Clone(bound = "P: Bls12Parameters"),
    Copy(bound = "P: Bls12Parameters"),
    Debug(bound = "P: Bls12Parameters")
)]
struct G2HomProjective<P: Bls12Parameters> {
    x: Fp2<P::Fp2Config>,
    y: Fp2<P::Fp2Config>,
    z: Fp2<P::Fp2Config>,
}

impl<P: Bls12Parameters> Default for G2Prepared<P> {
    fn default() -> Self {
        Self::from(G2Affine::<P>::prime_subgroup_generator())
    }
}

impl<P: Bls12Parameters> From<G2Affine<P>> for G2Prepared<P> {
    fn from(q: G2Affine<P>) -> Self {
        let two_inv = P::Fp::one().double().inverse().unwrap();
        match q.is_zero() {
            true => G2Prepared {
                ell_coeffs: vec![],
                infinity: true,
            },
            false => {
                let mut ell_coeffs = vec![];
                let mut r = G2HomProjective {
                    x: q.x,
                    y: q.y,
                    z: Fp2::one(),
                };

                for i in BitIteratorBE::new(P::X).skip(1) {
                    ell_coeffs.push(doubling_step::<P>(&mut r, &two_inv));

                    if i {
                        ell_coeffs.push(addition_step::<P>(&mut r, &q));
                    }
                }

                Self {
                    ell_coeffs,
                    infinity: false,
                }
            },
        }
    }
}

impl<P: Bls12Parameters> G2Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.infinity
    }
}

fn doubling_step<B: Bls12Parameters>(
    r: &mut G2HomProjective<B>,
    two_inv: &B::Fp,
) -> EllCoeff<Fp2<B::Fp2Config>> {
    // Formula for line function when working with
    // homogeneous projective coordinates.

    let mut a = r.x * &r.y;
    a.mul_assign_by_fp(two_inv);
    let b = r.y.square();
    let c = r.z.square();
    let e = B::G2Parameters::COEFF_B * &(c.double() + &c);
    let f = e.double() + &e;
    let mut g = b + &f;
    g.mul_assign_by_fp(two_inv);
    let h = (r.y + &r.z).square() - &(b + &c);
    let i = e - &b;
    let j = r.x.square();
    let e_square = e.square();

    r.x = a * &(b - &f);
    r.y = g.square() - &(e_square.double() + &e_square);
    r.z = b * &h;
    match B::TWIST_TYPE {
        TwistType::M => (i, j.double() + &j, -h),
        TwistType::D => (-h, j.double() + &j, i),
    }
}

fn addition_step<B: Bls12Parameters>(
    r: &mut G2HomProjective<B>,
    q: &G2Affine<B>,
) -> EllCoeff<Fp2<B::Fp2Config>> {
    let (&qx, &qy) = q.xy().unwrap();
    // Formula for line function when working with
    // homogeneous projective coordinates.
    let theta = r.y - &(qy * &r.z);
    let lambda = r.x - &(qx * &r.z);
    let c = theta.square();
    let d = lambda.square();
    let e = lambda * &d;
    let f = r.z * &c;
    let g = r.x * &d;
    let h = e + &f - &g.double();
    r.x = lambda * &h;
    r.y = theta * &(g - &h) - &(e * &r.y);
    r.z *= &e;
    let j = theta * &qx - &(lambda * &qy);

    match B::TWIST_TYPE {
        TwistType::M => (j, -theta, lambda),
        TwistType::D => (lambda, -theta, j),
    }
}
