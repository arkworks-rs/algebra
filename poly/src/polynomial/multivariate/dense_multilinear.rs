//! multilinear polynomial represented in evaluation form

use crate::polynomial::MultilinearPolynomialEvaluationForm;
use crate::{MVPolynomial, Polynomial};
use ark_ff::{Field, Zero};
use ark_std::fmt;
use ark_std::fmt::Formatter;
use ark_std::ops::{Add, AddAssign, Neg, Sub, SubAssign};
use ark_std::vec::Vec;
use rand::Rng;
// #[cfg(feature = "parallel")]
// use rayon::prelude::*; // todo: enable this
/// Stores a multilinear polynomial in dense evaluation form.
#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct DenseMultilinearPolynomial<F: Field> {
    /// The evaluation over {0,1}^n
    pub backing_array: Vec<F>,
    /// Number of variables
    pub num_vars: usize,
}

impl<F: Field> DenseMultilinearPolynomial<F> {
    /// Construct a new polynomial from a list of evaluations where the index represent a point.
    ///
    /// Index represents a point in {0,1}^`num_vars` in little endian form. For example, `0b1011` represents `P(1,1,0,1)`
    pub fn from_evaluations_slice(num_vars: usize, evaluations: &[F]) -> Self {
        Self::from_evaluations_vec(num_vars, evaluations.to_vec())
    }

    /// Construct a new polynomial from a list of evaluations where the index represent a point.
    ///
    /// Index represents a point in {0,1}^`num_vars` in little endian form. For example, `0b1011` represents `P(1,1,0,1)`
    pub fn from_evaluations_vec(_num_vars: usize, _evaluations: Vec<F>) -> Self {
        todo!()
    }
}

impl<F: Field> Polynomial<F> for DenseMultilinearPolynomial<F> {
    type Point = Vec<F>;

    /// return the total degree of the polynomial
    fn degree(&self) -> usize {
        todo!()
    }

    fn evaluate(&self, _point: &Self::Point) -> F {
        todo!()
    }
}

impl<F: Field> MVPolynomial<F> for DenseMultilinearPolynomial<F> {
    fn num_vars(&self) -> usize {
        todo!()
    }

    fn rand<R: Rng>(_d: usize, _num_vars: usize, _rng: &mut R) -> Self {
        todo!()
    }
}

impl<F: Field> MultilinearPolynomialEvaluationForm<F> for DenseMultilinearPolynomial<F> {
    fn lookup_evaluation(&self, _index: usize) -> F {
        todo!()
    }
}

impl<F: Field> Add for DenseMultilinearPolynomial<F> {
    type Output = DenseMultilinearPolynomial<F>;

    fn add(self, other: DenseMultilinearPolynomial<F>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, F: Field> Add<&'a DenseMultilinearPolynomial<F>>
    for &'b DenseMultilinearPolynomial<F>
{
    type Output = DenseMultilinearPolynomial<F>;

    fn add(self, _rhs: &'a DenseMultilinearPolynomial<F>) -> Self::Output {
        todo!()
    }
}

impl<F: Field> AddAssign for DenseMultilinearPolynomial<F> {
    fn add_assign(&mut self, other: Self) {
        *self = &*self + &other;
    }
}

impl<'a, 'b, F: Field> AddAssign<&'a DenseMultilinearPolynomial<F>>
    for DenseMultilinearPolynomial<F>
{
    fn add_assign(&mut self, other: &'a DenseMultilinearPolynomial<F>) {
        *self = &*self + other;
    }
}

impl<'a, 'b, F: Field> AddAssign<(F, &'a DenseMultilinearPolynomial<F>)>
    for DenseMultilinearPolynomial<F>
{
    fn add_assign(&mut self, (_f, _other): (F, &'a DenseMultilinearPolynomial<F>)) {
        let _other = todo!();
        // *self = &*self + &other;
    }
}

impl<F: Field> Neg for DenseMultilinearPolynomial<F> {
    type Output = ();

    fn neg(self) -> Self::Output {
        todo!()
    }
}

impl<F: Field> Sub for DenseMultilinearPolynomial<F> {
    type Output = DenseMultilinearPolynomial<F>;

    fn sub(self, other: DenseMultilinearPolynomial<F>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, F: Field> Sub<&'a DenseMultilinearPolynomial<F>>
    for &'b DenseMultilinearPolynomial<F>
{
    type Output = DenseMultilinearPolynomial<F>;

    fn sub(self, _rhs: &'a DenseMultilinearPolynomial<F>) -> Self::Output {
        todo!()
    }
}

impl<F: Field> SubAssign for DenseMultilinearPolynomial<F> {
    fn sub_assign(&mut self, other: Self) {
        *self = &*self - &other;
    }
}

impl<'a, 'b, F: Field> SubAssign<&'a DenseMultilinearPolynomial<F>>
    for DenseMultilinearPolynomial<F>
{
    fn sub_assign(&mut self, other: &'a DenseMultilinearPolynomial<F>) {
        *self = &*self + other;
    }
}

impl<F: Field> fmt::Debug for DenseMultilinearPolynomial<F> {
    fn fmt(&self, _f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        todo!()
    }
}

impl<F: Field> Zero for DenseMultilinearPolynomial<F> {
    fn zero() -> Self {
        todo!()
    }

    fn is_zero(&self) -> bool {
        todo!()
    }
}
