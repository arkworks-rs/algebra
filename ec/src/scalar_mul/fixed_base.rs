use ark_ff::{BigInteger, PrimeField};
use ark_std::{cfg_iter, cfg_iter_mut, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use super::ScalarMul;

pub struct FixedBase;

impl FixedBase {
    fn get_mul_window_size(num_scalars: usize) -> usize {
        if num_scalars < 32 {
            3
        } else {
            super::ln_without_floats(num_scalars)
        }
    }

    fn get_window_table<T: ScalarMul>(window: usize, g: T) -> Vec<Vec<T::MulBase>> {
        let scalar_size = T::ScalarField::MODULUS_BIT_SIZE as usize;
        let in_window = 1 << window;
        let outerc = (scalar_size + window - 1) / window;
        let last_in_window = 1 << (scalar_size - (outerc - 1) * window);

        let mut multiples_of_g = vec![vec![T::zero(); in_window]; outerc];

        let mut g_outer = g;
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
        cfg_iter!(multiples_of_g)
            .map(|s| T::batch_convert_to_mul_base(s))
            .collect()
    }

    fn windowed_mul<T: ScalarMul>(
        outerc: usize,
        window: usize,
        multiples_of_g: &[Vec<T::MulBase>],
        scalar: &T::ScalarField,
    ) -> T {
        let modulus_size = T::ScalarField::MODULUS_BIT_SIZE as usize;
        let scalar_val = scalar.into_bigint().to_bits_le();

        let mut res = T::from(multiples_of_g[0][0]);
        for outer in 0..outerc {
            let mut inner = 0usize;
            for i in 0..window {
                if outer * window + i < modulus_size && scalar_val[outer * window + i] {
                    inner |= 1 << i;
                }
            }
            res += &multiples_of_g[outer][inner];
        }
        res
    }

    /// Compute the vector v[0].G, v[1].G, ..., v[n-1].G given
    /// - a window size `window`
    /// - a pre-computed table from from `get_window_table` on G
    /// - a vector of scalars `v`
    /// using fixed-base multiplication
    /// # Example
    /// ```
    /// use ark_std::{One, UniformRand};
    /// use ark_ec::pairing::Pairing;
    /// use ark_test_curves::bls12_381::G1Projective as G;
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_ec::scalar_mul::fixed_base::FixedBase;
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
    /// let powers_of_g: Vec<G> = FixedBase::msm(g, &powers_of_s);
    /// let naive_powers_of_g: Vec<G> = powers_of_s.iter().map(|e| g * e).collect();
    /// assert_eq!(powers_of_g, naive_powers_of_g);
    /// ```
    pub fn msm<T: ScalarMul>(g: T, v: &[T::ScalarField]) -> Vec<T> {
        let window_size = Self::get_mul_window_size(v.len());
        let table = Self::get_window_table::<T>(window_size, g.clone());
        let scalar_size = T::ScalarField::MODULUS_BIT_SIZE as usize;
        let outerc = (scalar_size + window_size - 1) / window_size;
        assert!(outerc <= table.len());

        cfg_iter!(v)
            .map(|e| Self::windowed_mul::<T>(outerc, window_size, &table, e))
            .collect::<Vec<_>>()
    }
}
