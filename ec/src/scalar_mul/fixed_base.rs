use ark_ff::{BigInteger, PrimeField};
use ark_std::{cfg_iter, cfg_iter_mut, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use super::ScalarMul;

pub struct FixedBase;

impl FixedBase {
    pub fn get_mul_window_size(num_scalars: usize) -> usize {
        if num_scalars < 32 {
            3
        } else {
            super::ln_without_floats(num_scalars)
        }
    }

    pub fn get_window_table<T: ScalarMul>(
        scalar_size: usize,
        window: usize,
        g: T,
    ) -> Vec<Vec<T::MulBase>> {
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

    pub fn windowed_mul<T: ScalarMul>(
        outerc: usize,
        window: usize,
        multiples_of_g: &[Vec<<T as ScalarMul>::MulBase>],
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

    // TODO use const-generics for the scalar size and window
    // TODO use iterators of iterators of T::Affine instead of taking owned Vec
    pub fn msm<T: ScalarMul>(
        scalar_size: usize,
        window: usize,
        table: &[Vec<<T as ScalarMul>::MulBase>],
        v: &[T::ScalarField],
    ) -> Vec<T> {
        let outerc = (scalar_size + window - 1) / window;
        assert!(outerc <= table.len());

        cfg_iter!(v)
            .map(|e| Self::windowed_mul::<T>(outerc, window, table, e))
            .collect::<Vec<_>>()
    }
}
