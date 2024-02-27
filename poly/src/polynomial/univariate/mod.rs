//! Work with sparse and dense polynomials.

use crate::{DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial};
use ark_ff::{FftField, Field, Zero};
use ark_std::{borrow::Cow, vec::*};
use DenseOrSparsePolynomial::*;

mod dense;
mod sparse;

pub use dense::DensePolynomial;
pub use sparse::SparsePolynomial;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Represents either a sparse polynomial or a dense one.
#[derive(Clone)]
pub enum DenseOrSparsePolynomial<'a, F: Field> {
    /// Represents the case where `self` is a sparse polynomial
    SPolynomial(Cow<'a, SparsePolynomial<F>>),
    /// Represents the case where `self` is a dense polynomial
    DPolynomial(Cow<'a, DensePolynomial<F>>),
}

impl<'a, F: 'a + Field> From<DensePolynomial<F>> for DenseOrSparsePolynomial<'a, F> {
    fn from(other: DensePolynomial<F>) -> Self {
        DPolynomial(Cow::Owned(other))
    }
}

impl<'a, F: 'a + Field> From<&'a DensePolynomial<F>> for DenseOrSparsePolynomial<'a, F> {
    fn from(other: &'a DensePolynomial<F>) -> Self {
        DPolynomial(Cow::Borrowed(other))
    }
}

impl<'a, F: 'a + Field> From<SparsePolynomial<F>> for DenseOrSparsePolynomial<'a, F> {
    fn from(other: SparsePolynomial<F>) -> Self {
        SPolynomial(Cow::Owned(other))
    }
}

impl<'a, F: Field> From<&'a SparsePolynomial<F>> for DenseOrSparsePolynomial<'a, F> {
    fn from(other: &'a SparsePolynomial<F>) -> Self {
        SPolynomial(Cow::Borrowed(other))
    }
}

impl<'a, F: Field> From<DenseOrSparsePolynomial<'a, F>> for DensePolynomial<F> {
    fn from(other: DenseOrSparsePolynomial<'a, F>) -> DensePolynomial<F> {
        match other {
            DPolynomial(p) => p.into_owned(),
            SPolynomial(p) => p.into_owned().into(),
        }
    }
}

impl<'a, F: 'a + Field> TryInto<SparsePolynomial<F>> for DenseOrSparsePolynomial<'a, F> {
    type Error = ();

    fn try_into(self) -> Result<SparsePolynomial<F>, ()> {
        match self {
            SPolynomial(p) => Ok(p.into_owned()),
            _ => Err(()),
        }
    }
}

impl<'a, F: Field> DenseOrSparsePolynomial<'a, F> {
    /// Checks if the given polynomial is zero.
    pub fn is_zero(&self) -> bool {
        match self {
            SPolynomial(s) => s.is_zero(),
            DPolynomial(d) => d.is_zero(),
        }
    }

    /// Return the degree of `self.
    pub fn degree(&self) -> usize {
        match self {
            SPolynomial(s) => s.degree(),
            DPolynomial(d) => d.degree(),
        }
    }

    #[inline]
    fn leading_coefficient(&self) -> Option<&F> {
        match self {
            SPolynomial(p) => p.last().map(|(_, c)| c),
            DPolynomial(p) => p.last(),
        }
    }

    #[inline]
    fn iter_with_index(&self) -> Vec<(usize, F)> {
        match self {
            SPolynomial(p) => p.to_vec(),
            DPolynomial(p) => p.iter().cloned().enumerate().collect(),
        }
    }

    /// Divide self by another (sparse or dense) polynomial, and returns the
    /// quotient and remainder.
    pub fn divide_with_q_and_r(
        &self,
        divisor: &Self,
    ) -> Option<(DensePolynomial<F>, DensePolynomial<F>)> {
        if self.is_zero() {
            Some((DensePolynomial::zero(), DensePolynomial::zero()))
        } else if divisor.is_zero() {
            panic!("Dividing by zero polynomial")
        } else if self.degree() < divisor.degree() {
            Some((DensePolynomial::zero(), self.clone().into()))
        } else {
            // Now we know that self.degree() >= divisor.degree();
            let mut quotient = vec![F::zero(); self.degree() - divisor.degree() + 1];
            let mut remainder: DensePolynomial<F> = self.clone().into();
            // Can unwrap here because we know self is not zero.
            let divisor_leading_inv = divisor.leading_coefficient().unwrap().inverse().unwrap();
            while !remainder.is_zero() && remainder.degree() >= divisor.degree() {
                let cur_q_coeff = *remainder.coeffs.last().unwrap() * divisor_leading_inv;
                let cur_q_degree = remainder.degree() - divisor.degree();
                quotient[cur_q_degree] = cur_q_coeff;

                for (i, div_coeff) in divisor.iter_with_index() {
                    remainder[cur_q_degree + i] -= &(cur_q_coeff * div_coeff);
                }
                while let Some(true) = remainder.coeffs.last().map(|c| c.is_zero()) {
                    remainder.coeffs.pop();
                }
            }
            Some((DensePolynomial::from_coefficients_vec(quotient), remainder))
        }
    }
}
impl<'a, F: 'a + FftField> DenseOrSparsePolynomial<'a, F> {
    /// Construct `Evaluations` by evaluating a polynomial over the domain
    /// `domain`.
    pub fn evaluate_over_domain<D: EvaluationDomain<F>>(
        poly: impl Into<Self>,
        domain: D,
    ) -> Evaluations<F, D> {
        let poly = poly.into();
        poly.eval_over_domain_helper(domain)
    }

    fn eval_over_domain_helper<D: EvaluationDomain<F>>(self, domain: D) -> Evaluations<F, D> {
        let eval_sparse_poly = |s: &SparsePolynomial<F>| {
            let evals = domain.elements().map(|elem| s.evaluate(&elem)).collect();
            Evaluations::from_vec_and_domain(evals, domain)
        };

        match self {
            SPolynomial(Cow::Borrowed(s)) => eval_sparse_poly(s),
            SPolynomial(Cow::Owned(s)) => eval_sparse_poly(&s),
            DPolynomial(Cow::Borrowed(d)) => {
                if d.is_zero() {
                    Evaluations::zero(domain)
                } else {
                    let mut chunks = d.coeffs.chunks(domain.size());
                    let mut first = chunks.next().unwrap().to_vec();
                    let offset = domain.coset_offset();
                    // Reduce the coefficients of the polynomial mod X^domain.size()
                    for (i, chunk) in chunks.enumerate() {
                        if offset.is_one() {
                            cfg_iter_mut!(first).zip(chunk).for_each(|(x, y)| *x += y);
                        } else {
                            let offset_power = offset.pow(&[((i + 1) * domain.size()) as u64]);
                            cfg_iter_mut!(first)
                                .zip(chunk)
                                .for_each(|(x, y)| *x += offset_power * y);
                        }
                    }
                    domain.fft_in_place(&mut first);
                    Evaluations::from_vec_and_domain(first, domain)
                }
            },
            DPolynomial(Cow::Owned(mut d)) => {
                if d.is_zero() {
                    Evaluations::zero(domain)
                } else {
                    let mut chunks = d.coeffs.chunks_mut(domain.size());
                    let first = chunks.next().unwrap();
                    let offset = domain.coset_offset();
                    // Reduce the coefficients of the polynomial mod X^domain.size()
                    for (i, chunk) in chunks.enumerate() {
                        if offset.is_one() {
                            cfg_iter_mut!(first).zip(chunk).for_each(|(x, y)| *x += y);
                        } else {
                            let offset_power = offset.pow(&[((i + 1) * domain.size()) as u64]);
                            cfg_iter_mut!(first)
                                .zip(chunk)
                                .for_each(|(x, y)| *x += offset_power * y);
                        }
                    }
                    domain.fft_in_place(&mut d.coeffs);
                    Evaluations::from_vec_and_domain(d.coeffs, domain)
                }
            },
        }
    }
}
