pub mod glv;
pub mod wnaf;

pub mod variable_base;

use crate::{
    short_weierstrass::{Affine, Projective, SWCurveConfig},
    PrimeGroup,
};
use ark_ff::{AdditiveGroup, BigInteger, PrimeField, Zero};
use ark_std::{
    cfg_iter, cfg_iter_mut,
    ops::{Add, AddAssign, Mul, Neg, Sub, SubAssign},
    vec::*,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// The result of this function is only approximately `ln(a)`
/// [`Explanation of usage`]
///
/// [`Explanation of usage`]: https://github.com/scipr-lab/zexe/issues/79#issue-556220473
fn ln_without_floats(a: usize) -> usize {
    // log2(a) * ln(2)
    (ark_std::log2(a) * 69 / 100) as usize
}

/// Standard double-and-add method for multiplication by a scalar.
#[inline(always)]
pub fn sw_double_and_add_affine<P: SWCurveConfig>(
    base: &Affine<P>,
    scalar: impl AsRef<[u64]>,
) -> Projective<P> {
    let mut res = Projective::<P>::zero();
    for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
        res.double_in_place();
        if b {
            res += base
        }
    }

    res
}

/// Standard double-and-add method for multiplication by a scalar.
#[inline(always)]
pub fn sw_double_and_add_projective<P: SWCurveConfig>(
    base: &Projective<P>,
    scalar: impl AsRef<[u64]>,
) -> Projective<P> {
    let mut res = Projective::<P>::zero();
    for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
        res.double_in_place();
        if b {
            res += base
        }
    }

    res
}

pub trait ScalarMul:
    PrimeGroup
    + Add<Self::MulBase, Output = Self>
    + AddAssign<Self::MulBase>
    + for<'a> Add<&'a Self::MulBase, Output = Self>
    + for<'a> AddAssign<&'a Self::MulBase>
    + Sub<Self::MulBase, Output = Self>
    + SubAssign<Self::MulBase>
    + for<'a> Sub<&'a Self::MulBase, Output = Self>
    + for<'a> SubAssign<&'a Self::MulBase>
    + From<Self::MulBase>
{
    type MulBase: Send
        + Sync
        + Copy
        + Eq
        + core::hash::Hash
        + Mul<Self::ScalarField, Output = Self>
        + for<'a> Mul<&'a Self::ScalarField, Output = Self>
        + Neg<Output = Self::MulBase>
        + From<Self>;

    const NEGATION_IS_CHEAP: bool;

    fn batch_convert_to_mul_base(bases: &[Self]) -> Vec<Self::MulBase>;

    /// Compute the vector v[0].G, v[1].G, ..., v[n-1].G, given:
    /// - an element `g`
    /// - a list `v` of n scalars
    ///
    /// # Example
    /// ```
    /// use ark_std::{One, UniformRand};
    /// use ark_ec::pairing::Pairing;
    /// use ark_test_curves::bls12_381::G1Projective as G;
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_ec::scalar_mul::ScalarMul;
    ///
    /// // Compute G, s.G, s^2.G, ..., s^9.G
    /// let mut rng = ark_std::test_rng();
    /// let max_degree = 10;
    /// let s = Fr::rand(&mut rng);
    /// let g = G::rand(&mut rng);
    /// let mut powers_of_s = vec![Fr::one()];
    /// let mut cur = s;
    /// for _ in 0..max_degree {
    ///     powers_of_s.push(cur);
    ///     cur *= &s;
    /// }
    /// let powers_of_g = g.batch_mul(&powers_of_s);
    /// let naive_powers_of_g: Vec<G> = powers_of_s.iter().map(|e| g * e).collect();
    /// assert_eq!(powers_of_g, naive_powers_of_g);
    /// ```
    fn batch_mul(self, v: &[Self::ScalarField]) -> Vec<Self::MulBase> {
        let table = BatchMulPreprocessing::new(self, v.len());
        Self::batch_mul_with_preprocessing(&table, v)
    }

    /// Compute the vector v[0].G, v[1].G, ..., v[n-1].G, given:
    /// - an element `g`
    /// - a list `v` of n scalars
    ///
    /// This method allows the user to provide a precomputed table of multiples of `g`.
    /// A more ergonomic way to call this would be to use [`BatchMulPreprocessing::batch_mul`].
    ///
    /// # Example
    /// ```
    /// use ark_std::{One, UniformRand};
    /// use ark_ec::pairing::Pairing;
    /// use ark_test_curves::bls12_381::G1Projective as G;
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_ec::scalar_mul::*;
    ///
    /// // Compute G, s.G, s^2.G, ..., s^9.G
    /// let mut rng = ark_std::test_rng();
    /// let max_degree = 10;
    /// let s = Fr::rand(&mut rng);
    /// let g = G::rand(&mut rng);
    /// let mut powers_of_s = vec![Fr::one()];
    /// let mut cur = s;
    /// for _ in 0..max_degree {
    ///     powers_of_s.push(cur);
    ///     cur *= &s;
    /// }
    /// let table = BatchMulPreprocessing::new(g, powers_of_s.len());
    /// let powers_of_g = G::batch_mul_with_preprocessing(&table, &powers_of_s);
    /// let powers_of_g_2 = table.batch_mul(&powers_of_s);
    /// let naive_powers_of_g: Vec<G> = powers_of_s.iter().map(|e| g * e).collect();
    /// assert_eq!(powers_of_g, naive_powers_of_g);
    /// assert_eq!(powers_of_g_2, naive_powers_of_g);
    /// ```
    fn batch_mul_with_preprocessing(
        table: &BatchMulPreprocessing<Self>,
        v: &[Self::ScalarField],
    ) -> Vec<Self::MulBase> {
        table.batch_mul(v)
    }
}

/// Preprocessing used internally for batch scalar multiplication via [`ScalarMul::batch_mul`].
/// - `window` is the window size used for the precomputation
/// - `max_scalar_size` is the maximum size of the scalars that will be multiplied
/// - `table` is the precomputed table of multiples of `base`
pub struct BatchMulPreprocessing<T: ScalarMul> {
    pub window: usize,
    pub max_scalar_size: usize,
    pub table: Vec<Vec<T::MulBase>>,
}

impl<T: ScalarMul> BatchMulPreprocessing<T> {
    pub fn new(base: T, num_scalars: usize) -> Self {
        let scalar_size = T::ScalarField::MODULUS_BIT_SIZE as usize;
        Self::with_num_scalars_and_scalar_size(base, num_scalars, scalar_size)
    }

    pub fn with_num_scalars_and_scalar_size(
        base: T,
        num_scalars: usize,
        max_scalar_size: usize,
    ) -> Self {
        let window = Self::compute_window_size(num_scalars);
        let in_window = 1 << window;
        let outerc = (max_scalar_size + window - 1) / window;
        let last_in_window = 1 << (max_scalar_size - (outerc - 1) * window);

        let mut multiples_of_g = vec![vec![T::zero(); in_window]; outerc];

        let mut g_outer = base;
        let mut g_outers = Vec::with_capacity(outerc);
        for _ in 0..outerc {
            g_outers.push(g_outer);
            for _ in 0..window {
                g_outer.double_in_place();
            }
        }
        cfg_iter_mut!(multiples_of_g)
            .enumerate()
            .take(outerc)
            .zip(g_outers)
            .for_each(|((outer, multiples_of_g), g_outer)| {
                let cur_in_window = if outer == outerc - 1 {
                    last_in_window
                } else {
                    in_window
                };

                let mut g_inner = T::zero();
                for inner in multiples_of_g.iter_mut().take(cur_in_window) {
                    *inner = g_inner;
                    g_inner += &g_outer;
                }
            });
        let table = cfg_iter!(multiples_of_g)
            .map(|s| T::batch_convert_to_mul_base(s))
            .collect();
        Self {
            window,
            max_scalar_size,
            table,
        }
    }

    pub fn compute_window_size(num_scalars: usize) -> usize {
        if num_scalars < 32 {
            3
        } else {
            ln_without_floats(num_scalars)
        }
    }

    pub fn batch_mul(&self, v: &[T::ScalarField]) -> Vec<T::MulBase> {
        let result: Vec<_> = cfg_iter!(v).map(|e| self.windowed_mul(e)).collect();
        T::batch_convert_to_mul_base(&result)
    }

    fn windowed_mul(&self, scalar: &T::ScalarField) -> T {
        let outerc = (self.max_scalar_size + self.window - 1) / self.window;
        let modulus_size = T::ScalarField::MODULUS_BIT_SIZE as usize;
        let scalar_val = scalar.into_bigint().to_bits_le();

        let mut res = T::from(self.table[0][0]);
        for outer in 0..outerc {
            let mut inner = 0usize;
            for i in 0..self.window {
                if outer * self.window + i < modulus_size && scalar_val[outer * self.window + i] {
                    inner |= 1 << i;
                }
            }
            res += &self.table[outer][inner];
        }
        res
    }
}
