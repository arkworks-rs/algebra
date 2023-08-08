use ark_std::{cfg_iter, cfg_iter_mut, vec::Vec};

use itertools::Itertools;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::{
    bits::BitIteratorLE,
    module::{Scalar, ScalarExp, ScalarMul},
};

pub struct FixedBase;

impl FixedBase {
    pub fn get_mul_window_size(num_scalars: usize) -> usize {
        if num_scalars < 32 {
            3
        } else {
            super::ln_without_floats(num_scalars)
        }
    }

    pub fn get_window_table_additive<T: ScalarMul<S>, S: Scalar>(
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

    pub fn windowed_mul<T: ScalarMul<S>, S: Scalar>(
        outerc: usize,
        window: usize,
        multiples_of_g: &[Vec<T::MulBase>],
        scalar: &S,
    ) -> T {
        let modulus_size =
            S::MAX_BIT_SIZE.expect("can only exponentiate with fixed-size scalars") as usize;
        let (sign, scalar_u64s) = scalar.as_u64s();
        let scalar_val = BitIteratorLE::new(scalar_u64s).collect_vec();

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
        if sign.is_negative() {
            res.neg_in_place();
        }
        res
    }

    // TODO use const-generics for the scalar size and window
    // TODO use iterators of iterators of T::Affine instead of taking owned Vec
    pub fn msm<T: ScalarMul<S>, S: Scalar>(
        scalar_size: usize,
        window: usize,
        table: &[Vec<T::MulBase>],
        v: &[S],
    ) -> Vec<T> {
        let outerc = (scalar_size + window - 1) / window;
        assert!(outerc <= table.len());

        cfg_iter!(v)
            .map(|e| Self::windowed_mul(outerc, window, table, e))
            .collect::<Vec<_>>()
    }
}

impl FixedBase {
    pub fn get_window_table_multiplicative<T: ScalarExp<S>, S: Scalar>(
        scalar_size: usize,
        window: usize,
        g: T,
    ) -> Vec<Vec<T::ExpBase>> {
        let in_window = 1 << window;
        let outerc = (scalar_size + window - 1) / window;
        let last_in_window = 1 << (scalar_size - (outerc - 1) * window);

        let mut multiples_of_g = vec![vec![T::one(); in_window]; outerc];

        let mut g_outer = g;
        let mut g_outers = Vec::with_capacity(outerc);
        for _ in 0..outerc {
            g_outers.push(g_outer);
            for _ in 0..window {
                g_outer.square_in_place();
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

                let mut g_inner = T::one();
                for inner in multiples_of_g.iter_mut().take(cur_in_window) {
                    *inner = g_inner;
                    g_inner *= &g_outer;
                }
            });
        cfg_iter!(multiples_of_g)
            .map(|s| T::batch_convert_to_exp_base(s))
            .collect()
    }

    pub fn windowed_exp<T: ScalarExp<S>, S: Scalar>(
        outerc: usize,
        window: usize,
        powers_of_g: &[Vec<T::ExpBase>],
        exp: &S,
    ) -> T {
        let modulus_size =
            S::MAX_BIT_SIZE.expect("can only exponentiate with fixed-size scalars") as usize;
        let (sign, scalar_u64s) = exp.as_u64s();
        let scalar_val = BitIteratorLE::new(scalar_u64s).collect_vec();

        let mut res = T::from(powers_of_g[0][0]);
        for outer in 0..outerc {
            let mut inner = 0usize;
            for i in 0..window {
                if outer * window + i < modulus_size && scalar_val[outer * window + i] {
                    inner |= 1 << i;
                }
            }
            res *= &powers_of_g[outer][inner];
        }
        res
    }

    // TODO use const-generics for the scalar size and window
    // TODO use iterators of iterators of T::Affine instead of taking owned Vec
    pub fn mexp<T: ScalarExp<S>, S: Scalar>(
        exp_size: usize,
        window: usize,
        table: &[Vec<T::ExpBase>],
        v: &[S],
    ) -> Vec<T> {
        let outerc = (exp_size + window - 1) / window;
        assert!(outerc <= table.len());

        cfg_iter!(v)
            .map(|e| Self::windowed_exp::<T, S>(outerc, window, table, e))
            .collect::<Vec<_>>()
    }
}
