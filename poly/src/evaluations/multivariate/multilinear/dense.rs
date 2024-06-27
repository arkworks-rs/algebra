//! Multilinear polynomial represented in dense evaluation form.

use crate::{
    evaluations::multivariate::multilinear::{swap_bits, MultilinearExtension},
    Polynomial,
};
use ark_ff::{Field, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    fmt,
    fmt::Formatter,
    iter::IntoIterator,
    log2,
    ops::{Add, AddAssign, Index, Mul, MulAssign, Neg, Sub, SubAssign},
    rand::Rng,
    slice::{Iter, IterMut},
    vec::*,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Stores a multilinear polynomial in dense evaluation form.
#[derive(Clone, PartialEq, Eq, Hash, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct DenseMultilinearExtension<F: Field> {
    /// The evaluation over {0,1}^`num_vars`
    pub evaluations: Vec<F>,
    /// Number of variables
    pub num_vars: usize,
}

impl<F: Field> DenseMultilinearExtension<F> {
    /// Construct a new polynomial from a list of evaluations where the index
    /// represents a point in {0,1}^`num_vars` in little endian form. For
    /// example, `0b1011` represents `P(1,1,0,1)`
    pub fn from_evaluations_slice(num_vars: usize, evaluations: &[F]) -> Self {
        Self::from_evaluations_vec(num_vars, evaluations.to_vec())
    }

    /// Construct a new polynomial from a list of evaluations where the index
    /// represents a point in {0,1}^`num_vars` in little endian form. For
    /// example, `0b1011` represents `P(1,1,0,1)`.
    ///
    /// # Example
    /// ```
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_poly::{MultilinearExtension, Polynomial, DenseMultilinearExtension};
    ///
    /// // Construct a 2-variate MLE, which takes value 1 at (x_0, x_1) = (0, 1)
    /// // (i.e. 0b01, or index 2 in little endian)
    /// // f1(x_0, x_1) = x_1*(1-x_0)
    /// let mle = DenseMultilinearExtension::from_evaluations_vec(
    ///     2, vec![0, 0, 1, 0].iter().map(|x| Fr::from(*x as u64)).collect()
    /// );
    /// let eval = mle.evaluate(&vec![Fr::from(-2), Fr::from(17)]); // point = (x_0, x_1)
    /// assert_eq!(eval, Fr::from(51));
    /// ```
    pub fn from_evaluations_vec(num_vars: usize, evaluations: Vec<F>) -> Self {
        // assert that the number of variables matches the size of evaluations
        assert_eq!(
            evaluations.len(),
            1 << num_vars,
            "The size of evaluations should be 2^num_vars."
        );

        Self {
            num_vars,
            evaluations,
        }
    }
    /// Relabel the point in place by switching `k` scalars from position `a` to
    /// position `b`, and from position `b` to position `a` in vector.
    ///
    /// This function turns `P(x_1,...,x_a,...,x_{a+k - 1},...,x_b,...,x_{b+k - 1},...,x_n)`
    /// to `P(x_1,...,x_b,...,x_{b+k - 1},...,x_a,...,x_{a+k - 1},...,x_n)`
    pub fn relabel_in_place(&mut self, mut a: usize, mut b: usize, k: usize) {
        // enforce order of a and b
        if a > b {
            ark_std::mem::swap(&mut a, &mut b);
        }
        if a == b || k == 0 {
            return;
        }
        assert!(b + k <= self.num_vars, "invalid relabel argument");
        assert!(a + k <= b, "overlapped swap window is not allowed");
        for i in 0..self.evaluations.len() {
            let j = swap_bits(i, a, b, k);
            if i < j {
                self.evaluations.swap(i, j);
            }
        }
    }

    /// Returns an iterator that iterates over the evaluations over {0,1}^`num_vars`
    pub fn iter(&self) -> Iter<'_, F> {
        self.evaluations.iter()
    }

    /// Returns a mutable iterator that iterates over the evaluations over {0,1}^`num_vars`
    pub fn iter_mut(&mut self) -> IterMut<'_, F> {
        self.evaluations.iter_mut()
    }

    /// Concatenate the evaluation tables of multiple polynomials.
    /// If the combined table size is not a power of two, pad the table with zeros.
    ///
    /// # Example
    /// ```
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_poly::{MultilinearExtension, Polynomial, DenseMultilinearExtension};
    /// use ark_ff::One;
    ///
    /// // Construct a 2-variate multilinear polynomial f1
    /// // f1(x_0, x_1) = 2*(1-x_1)*(1-x_0) + 3*(1-x_1)*x_0 + 2*x_1*(1-x_0) + 6*x_1*x_0
    /// let mle_1 = DenseMultilinearExtension::from_evaluations_vec(
    ///     2, vec![2, 3, 2, 6].iter().map(|x| Fr::from(*x as u64)).collect()
    /// );
    /// // Construct another 2-variate MLE f2
    /// // f2(x_0, x_1) = 1*x_1*x_0
    /// let mle_2 = DenseMultilinearExtension::from_evaluations_vec(
    ///   2, vec![0, 0, 0, 1].iter().map(|x| Fr::from(*x as u64)).collect()
    /// );
    /// let mle = DenseMultilinearExtension::concat(&[&mle_1, &mle_2]);
    /// // The resulting polynomial is 3-variate:
    /// // f3(x_0, x_1, x_2) = (1 - x_2)*f1(x_0, x_1) + x_2*f2(x_0, x_1)
    /// // Evaluate it at a random point (1, 17, 3)
    /// let point = vec![Fr::one(), Fr::from(17), Fr::from(3)];
    /// let eval_1 = mle_1.evaluate(&point[..2].to_vec());
    /// let eval_2 = mle_2.evaluate(&point[..2].to_vec());
    /// let eval_combined = mle.evaluate(&point);
    ///
    /// assert_eq!(eval_combined, (Fr::one() - point[2]) * eval_1 + point[2] * eval_2);
    pub fn concat(polys: impl IntoIterator<Item = impl AsRef<Self>> + Clone) -> Self {
        // for efficient allocation into the concatenated vector, we need to know the total length
        // in advance, so we actually need to iterate twice. Cloning the iterator is cheap.
        let polys_iter_cloned = polys.clone().into_iter();

        let total_len: usize = polys
            .into_iter()
            .map(|poly| poly.as_ref().evaluations.len())
            .sum();

        let next_pow_of_two = total_len.next_power_of_two();
        let num_vars = log2(next_pow_of_two);
        let mut evaluations: Vec<F> = Vec::with_capacity(next_pow_of_two);

        for poly in polys_iter_cloned {
            evaluations.extend_from_slice(&poly.as_ref().evaluations.as_slice());
        }

        evaluations.resize(next_pow_of_two, F::zero());

        Self::from_evaluations_slice(num_vars as usize, &evaluations)
    }
}

impl<F: Field> AsRef<DenseMultilinearExtension<F>> for DenseMultilinearExtension<F> {
    fn as_ref(&self) -> &DenseMultilinearExtension<F> {
        self
    }
}

impl<F: Field> MultilinearExtension<F> for DenseMultilinearExtension<F> {
    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn rand<R: Rng>(num_vars: usize, rng: &mut R) -> Self {
        Self::from_evaluations_vec(
            num_vars,
            (0..(1 << num_vars)).map(|_| F::rand(rng)).collect(),
        )
    }

    fn relabel(&self, a: usize, b: usize, k: usize) -> Self {
        let mut copied = self.clone();
        copied.relabel_in_place(a, b, k);
        copied
    }

    /// Return the MLE resulting from binding the first variables of self
    /// to the values in `partial_point` (from left to right).
    ///
    /// Note: this method can be used in combination with `relabel` or
    /// `relabel_in_place` to bind variables at arbitrary positions.
    ///
    /// ```
    /// use ark_test_curves::bls12_381::Fr;
    /// # use ark_poly::{MultilinearExtension, DenseMultilinearExtension};
    ///
    /// // Constructing the two-variate multilinear polynomial x_0 + 2 * x_1 + 3 * x_0 * x_1
    /// // by specifying its evaluations at [00, 10, 01, 11]
    /// let mle = DenseMultilinearExtension::from_evaluations_vec(
    ///     2, vec![0, 1, 2, 6].iter().map(|x| Fr::from(*x as u64)).collect()
    /// );
    ///
    /// // Bind the first variable of the MLE, x_0, to the value 5, resulting in
    /// // a new polynomial in one variable: 5 + 17 * x
    /// let bound = mle.fix_variables(&[Fr::from(5)]);
    ///
    /// assert_eq!(bound.to_evaluations(), vec![Fr::from(5), Fr::from(22)]);
    /// ```
    /// }
    fn fix_variables(&self, partial_point: &[F]) -> Self {
        assert!(
            partial_point.len() <= self.num_vars,
            "invalid size of partial point"
        );
        let mut poly = self.evaluations.to_vec();
        let nv = self.num_vars;
        let dim = partial_point.len();
        // evaluate single variable of partial point from left to right
        for i in 1..dim + 1 {
            let r = partial_point[i - 1];
            for b in 0..(1 << (nv - i)) {
                let left = poly[b << 1];
                let right = poly[(b << 1) + 1];
                poly[b] = left + r * (right - left);
            }
        }
        Self::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
    }

    fn to_evaluations(&self) -> Vec<F> {
        self.evaluations.to_vec()
    }
}

impl<F: Field> Index<usize> for DenseMultilinearExtension<F> {
    type Output = F;

    /// Returns the evaluation of the polynomial at a point represented by index.
    ///
    /// Index represents a vector in {0,1}^`num_vars` in little endian form. For
    /// example, `0b1011` represents `P(1,1,0,1)`
    ///
    /// For dense multilinear polynomial, `index` takes constant time.
    fn index(&self, index: usize) -> &Self::Output {
        &self.evaluations[index]
    }
}

impl<F: Field> Add for DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn add(self, other: DenseMultilinearExtension<F>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, F: Field> Add<&'a DenseMultilinearExtension<F>> for &'b DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn add(self, rhs: &'a DenseMultilinearExtension<F>) -> Self::Output {
        // handle constant zero case
        if rhs.is_zero() {
            return self.clone();
        }
        if self.is_zero() {
            return rhs.clone();
        }
        assert_eq!(self.num_vars, rhs.num_vars);
        let result: Vec<F> = cfg_iter!(self.evaluations)
            .zip(cfg_iter!(rhs.evaluations))
            .map(|(a, b)| *a + *b)
            .collect();

        Self::Output::from_evaluations_vec(self.num_vars, result)
    }
}

impl<F: Field> AddAssign for DenseMultilinearExtension<F> {
    fn add_assign(&mut self, other: Self) {
        *self = &*self + &other;
    }
}

impl<'a, F: Field> AddAssign<&'a DenseMultilinearExtension<F>> for DenseMultilinearExtension<F> {
    fn add_assign(&mut self, other: &'a DenseMultilinearExtension<F>) {
        *self = &*self + other;
    }
}

impl<'a, F: Field> AddAssign<(F, &'a DenseMultilinearExtension<F>)>
    for DenseMultilinearExtension<F>
{
    fn add_assign(&mut self, (f, other): (F, &'a DenseMultilinearExtension<F>)) {
        let other = Self {
            num_vars: other.num_vars,
            evaluations: cfg_iter!(other.evaluations).map(|x| f * x).collect(),
        };
        *self = &*self + &other;
    }
}

impl<F: Field> Neg for DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn neg(self) -> Self::Output {
        Self::Output {
            num_vars: self.num_vars,
            evaluations: cfg_iter!(self.evaluations).map(|x| -*x).collect(),
        }
    }
}

impl<F: Field> Sub for DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn sub(self, other: DenseMultilinearExtension<F>) -> Self {
        &self - &other
    }
}

impl<'a, 'b, F: Field> Sub<&'a DenseMultilinearExtension<F>> for &'b DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn sub(self, rhs: &'a DenseMultilinearExtension<F>) -> Self::Output {
        self + &rhs.clone().neg()
    }
}

impl<F: Field> SubAssign for DenseMultilinearExtension<F> {
    fn sub_assign(&mut self, other: Self) {
        *self = &*self - &other;
    }
}

impl<'a, F: Field> SubAssign<&'a DenseMultilinearExtension<F>> for DenseMultilinearExtension<F> {
    fn sub_assign(&mut self, other: &'a DenseMultilinearExtension<F>) {
        *self = &*self - other;
    }
}

impl<F: Field> Mul<F> for DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn mul(self, scalar: F) -> Self::Output {
        &self * &scalar
    }
}

impl<'a, 'b, F: Field> Mul<&'a F> for &'b DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn mul(self, scalar: &'a F) -> Self::Output {
        if scalar.is_zero() {
            return DenseMultilinearExtension::zero();
        } else if scalar.is_one() {
            return self.clone();
        }
        let result: Vec<F> = self.evaluations.iter().map(|&x| x * scalar).collect();

        DenseMultilinearExtension {
            num_vars: self.num_vars,
            evaluations: result,
        }
    }
}

impl<F: Field> MulAssign<F> for DenseMultilinearExtension<F> {
    fn mul_assign(&mut self, scalar: F) {
        *self = &*self * &scalar
    }
}

impl<'a, F: Field> MulAssign<&'a F> for DenseMultilinearExtension<F> {
    fn mul_assign(&mut self, scalar: &'a F) {
        *self = &*self * scalar
    }
}

impl<F: Field> fmt::Debug for DenseMultilinearExtension<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "DenseML(nv = {}, evaluations = [", self.num_vars)?;
        for i in 0..ark_std::cmp::min(4, self.evaluations.len()) {
            write!(f, "{:?} ", self.evaluations[i])?;
        }
        if self.evaluations.len() < 4 {
            write!(f, "])")?;
        } else {
            write!(f, "...])")?;
        }
        Ok(())
    }
}

impl<F: Field> Zero for DenseMultilinearExtension<F> {
    fn zero() -> Self {
        Self {
            num_vars: 0,
            evaluations: vec![F::zero()],
        }
    }

    fn is_zero(&self) -> bool {
        self.num_vars == 0 && self.evaluations[0].is_zero()
    }
}

impl<F: Field> Polynomial<F> for DenseMultilinearExtension<F> {
    type Point = Vec<F>;

    fn degree(&self) -> usize {
        self.num_vars
    }

    /// Evaluate the dense MLE at the given point
    /// # Example
    /// ```
    /// use ark_test_curves::bls12_381::Fr;
    /// # use ark_poly::{MultilinearExtension, DenseMultilinearExtension, Polynomial};
    /// # use ark_ff::One;
    ///
    /// // The two-variate polynomial p = x_0 + 3 * x_0 * x_1 + 2 evaluates to [2, 3, 2, 6]
    /// // in the two-dimensional hypercube with points [00, 10, 01, 11]:
    /// // p(x_0, x_1) = 2*(1-x_1)*(1-x_0) + 3*(1-x_1)*x_0 + 2*x_1*(1-x_0) + 6*x_1*x_0
    /// let mle = DenseMultilinearExtension::from_evaluations_vec(
    ///     2, vec![2, 3, 2, 6].iter().map(|x| Fr::from(*x as u64)).collect()
    /// );
    ///
    /// // By the uniqueness of MLEs, `mle` is precisely the above polynomial, which
    /// // takes the value 54 at the point (x_0, x_1) = (1, 17)
    /// let eval = mle.evaluate(&[Fr::one(), Fr::from(17)].into());
    /// assert_eq!(eval, Fr::from(54));
    /// ```
    fn evaluate(&self, point: &Self::Point) -> F {
        assert!(point.len() == self.num_vars);
        self.fix_variables(&point)[0]
    }
}

#[cfg(test)]
mod tests {
    use crate::{DenseMultilinearExtension, MultilinearExtension, Polynomial};
    use ark_ff::{Field, One, Zero};
    use ark_std::{ops::Neg, test_rng, vec::*, UniformRand};
    use ark_test_curves::bls12_381::Fr;

    /// utility: evaluate multilinear extension (in form of data array) at a random point
    fn evaluate_data_array<F: Field>(data: &[F], point: &[F]) -> F {
        if data.len() != (1 << point.len()) {
            panic!("Data size mismatch with number of variables. ")
        }

        let nv = point.len();
        let mut a = data.to_vec();

        for i in 1..nv + 1 {
            let r = point[i - 1];
            for b in 0..(1 << (nv - i)) {
                a[b] = a[b << 1] * (F::one() - r) + a[(b << 1) + 1] * r;
            }
        }
        a[0]
    }

    #[test]
    fn evaluate_at_a_point() {
        let mut rng = test_rng();
        let poly = DenseMultilinearExtension::rand(10, &mut rng);
        for _ in 0..10 {
            let point: Vec<_> = (0..10).map(|_| Fr::rand(&mut rng)).collect();
            assert_eq!(
                evaluate_data_array(&poly.evaluations, &point),
                poly.evaluate(&point)
            )
        }
    }

    #[test]
    fn relabel_polynomial() {
        let mut rng = test_rng();
        for _ in 0..20 {
            let mut poly = DenseMultilinearExtension::rand(10, &mut rng);
            let mut point: Vec<_> = (0..10).map(|_| Fr::rand(&mut rng)).collect();

            let expected = poly.evaluate(&point);

            poly.relabel_in_place(2, 2, 1); // should have no effect
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_in_place(3, 4, 1); // should switch 3 and 4
            point.swap(3, 4);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_in_place(7, 5, 1);
            point.swap(7, 5);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_in_place(2, 5, 3);
            point.swap(2, 5);
            point.swap(3, 6);
            point.swap(4, 7);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_in_place(7, 0, 2);
            point.swap(0, 7);
            point.swap(1, 8);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_in_place(0, 9, 1);
            point.swap(0, 9);
            assert_eq!(expected, poly.evaluate(&point));
        }
    }

    #[test]
    fn arithmetic() {
        const NV: usize = 10;
        let mut rng = test_rng();
        for _ in 0..20 {
            let scalar = Fr::rand(&mut rng);
            let point: Vec<_> = (0..NV).map(|_| Fr::rand(&mut rng)).collect();
            let poly1 = DenseMultilinearExtension::rand(NV, &mut rng);
            let poly2 = DenseMultilinearExtension::rand(NV, &mut rng);
            let v1 = poly1.evaluate(&point);
            let v2 = poly2.evaluate(&point);
            // test add
            assert_eq!((&poly1 + &poly2).evaluate(&point), v1 + v2);
            // test sub
            assert_eq!((&poly1 - &poly2).evaluate(&point), v1 - v2);
            // test negate
            assert_eq!(poly1.clone().neg().evaluate(&point), -v1);
            // test mul poly by scalar
            assert_eq!((&poly1 * &scalar).evaluate(&point), v1 * scalar);
            // test add assign
            {
                let mut poly1 = poly1.clone();
                poly1 += &poly2;
                assert_eq!(poly1.evaluate(&point), v1 + v2)
            }
            // test sub assign
            {
                let mut poly1 = poly1.clone();
                poly1 -= &poly2;
                assert_eq!(poly1.evaluate(&point), v1 - v2)
            }
            // test add assign with scalar
            {
                let mut poly1 = poly1.clone();
                let scalar = Fr::rand(&mut rng);
                poly1 += (scalar, &poly2);
                assert_eq!(poly1.evaluate(&point), v1 + scalar * v2)
            }
            // test additive identity
            {
                assert_eq!(&poly1 + &DenseMultilinearExtension::zero(), poly1);
                assert_eq!(&DenseMultilinearExtension::zero() + &poly1, poly1);
                {
                    let mut poly1_cloned = poly1.clone();
                    poly1_cloned += &DenseMultilinearExtension::zero();
                    assert_eq!(&poly1_cloned, &poly1);
                    let mut zero = DenseMultilinearExtension::zero();
                    let scalar = Fr::rand(&mut rng);
                    zero += (scalar, &poly1);
                    assert_eq!(zero.evaluate(&point), scalar * v1);
                }
            }
            // test mul_assign for poly * scalar
            {
                let mut poly1_cloned = poly1.clone();
                poly1_cloned *= Fr::one();
                assert_eq!(poly1_cloned.evaluate(&point), v1);
                poly1_cloned *= scalar;
                assert_eq!(poly1_cloned.evaluate(&point), v1 * scalar);
                poly1_cloned *= Fr::zero();
                assert_eq!(poly1_cloned, DenseMultilinearExtension::zero());
            }
        }
    }

    #[test]
    fn concat_two_equal_polys() {
        let mut rng = test_rng();
        let degree = 10;

        let poly_l = DenseMultilinearExtension::rand(degree, &mut rng);
        let poly_r = DenseMultilinearExtension::rand(degree, &mut rng);

        let merged = DenseMultilinearExtension::concat(&[&poly_l, &poly_r]);
        for _ in 0..10 {
            let point: Vec<_> = (0..(degree + 1)).map(|_| Fr::rand(&mut rng)).collect();

            let expected = (Fr::ONE - point[10]) * poly_l.evaluate(&point[..10].to_vec())
                + point[10] * poly_r.evaluate(&point[..10].to_vec());
            assert_eq!(expected, merged.evaluate(&point));
        }
    }

    #[test]
    fn concat_unequal_polys() {
        let mut rng = test_rng();
        let degree = 10;
        let poly_l = DenseMultilinearExtension::rand(degree, &mut rng);
        // smaller poly
        let poly_r = DenseMultilinearExtension::rand(degree - 1, &mut rng);

        let merged = DenseMultilinearExtension::concat(&[&poly_l, &poly_r]);

        for _ in 0..10 {
            let point: Vec<_> = (0..(degree + 1)).map(|_| Fr::rand(&mut rng)).collect();

            // merged poly is (1-x_10)*poly_l + x_10*((1-x_9)*poly_r1 + x_9*poly_r2).
            // where poly_r1 is poly_r, and poly_r2 is all zero, since we are padding.
            let expected = (Fr::ONE - point[10]) * poly_l.evaluate(&point[..10].to_vec())
                + point[10] * ((Fr::ONE - point[9]) * poly_r.evaluate(&point[..9].to_vec()));
            assert_eq!(expected, merged.evaluate(&point));
        }
    }

    #[test]
    fn concat_two_iterators() {
        let mut rng = test_rng();
        let degree = 10;

        // rather than merging two polynomials, we merge two iterators of polynomials
        let polys_l: Vec<_> = (0..2)
            .map(|_| DenseMultilinearExtension::rand(degree - 2, &mut test_rng()))
            .collect();
        let polys_r: Vec<_> = (0..2)
            .map(|_| DenseMultilinearExtension::rand(degree - 2, &mut test_rng()))
            .collect();

        let merged = DenseMultilinearExtension::<Fr>::concat(polys_l.iter().chain(polys_r.iter()));

        for _ in 0..10 {
            let point: Vec<_> = (0..(degree)).map(|_| Fr::rand(&mut rng)).collect();

            let expected = (Fr::ONE - point[9])
                * ((Fr::ONE - point[8]) * polys_l[0].evaluate(&point[..8].to_vec())
                    + point[8] * polys_l[1].evaluate(&point[..8].to_vec()))
                + point[9]
                    * ((Fr::ONE - point[8]) * polys_r[0].evaluate(&point[..8].to_vec())
                        + point[8] * polys_r[1].evaluate(&point[..8].to_vec()));

            assert_eq!(expected, merged.evaluate(&point));
        }
    }
}
