use ark_std::{cfg_chunks, vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::scalar_mul::{
    ln_without_floats,
    variable_base::{utils::*, VariableBaseMSM},
};

fn msm_small_serial<V: VariableBaseMSM, T: Into<u64> + Copy + Send + Sync>(
    mut bases: &[V::MulBase],
    mut scalars: &[T],
) -> V {
    let size = bases.len().min(scalars.len());
    if size == 0 {
        return V::zero();
    }

    bases = &bases[..size];
    scalars = &scalars[..size];
    let num_bits = core::mem::size_of::<T>() * 8;
    let c = compute_c(size);
    let zero = V::ZERO_BUCKET;

    // Each window is of size `c`.
    // We divide up the bits 0..num_bits into windows of size `c`, and
    // in parallel process each such window.
    let two_to_c = 1 << c;
    let window_sums: Vec<_> = (0..num_bits)
        .step_by(c)
        .map(|w_start| {
            let mut res = zero;
            // We don't need the "zero" bucket, so we only have 2^c - 1 buckets.
            let mut buckets = vec![zero; two_to_c - 1];
            // This clone is cheap, because the iterator contains just a
            // pointer and an index into the original vectors.
            scalars
                .iter()
                .zip(bases)
                .filter_map(|(&s, b)| {
                    let s = s.into();
                    (s != 0).then_some((s, b))
                })
                .for_each(|(scalar, base)| {
                    if scalar == 1 {
                        // We only process unit scalars once in the first window.
                        if w_start == 0 {
                            res += base;
                        }
                    } else {
                        let mut scalar = scalar;

                        // We right-shift by w_start, thus getting rid of the
                        // lower bits.
                        scalar >>= w_start as u32;

                        // We mod the remaining bits by 2^{window size}, thus taking `c` bits.
                        scalar %= two_to_c as u64;

                        // If the scalar is non-zero, we update the corresponding
                        // bucket.
                        // (Recall that `buckets` doesn't have a zero bucket.)
                        if scalar != 0 {
                            buckets[(scalar - 1) as usize] += base;
                        }
                    }
                });

            // Compute sum_{i in 0..num_buckets} (sum_{j in i..num_buckets} bucket[j])
            // This is computed below for b buckets, using 2b curve additions.
            //
            // We could first normalize `buckets` and then use mixed-addition
            // here, but that's slower for the kinds of groups we care about
            // (Short Weierstrass curves and Twisted Edwards curves).
            // In the case of Short Weierstrass curves,
            // mixed addition saves ~4 field multiplications per addition.
            // However normalization (with the inversion batched) takes ~6
            // field multiplications per element,
            // hence batch normalization is a slowdown.

            // `running_sum` = sum_{j in i..num_buckets} bucket[j],
            // where we iterate backward from i = num_buckets to 0.
            let mut running_sum = V::ZERO_BUCKET;
            buckets.into_iter().rev().for_each(|b| {
                running_sum += &b;
                res += &running_sum;
            });
            res
        })
        .collect();

    // We store the sum for the highest window.
    let mut total: V = (*window_sums.last().unwrap()).into();
    for i in (0..(window_sums.len() - 1)).rev() {
        for _ in 0..c {
            total.double_in_place();
        }
        total += &window_sums[i];
    }

    total
}

/// Computes multi-scalar multiplication where the scalars
/// lie in the range {-1, 0, 1}.
pub(super) fn msm_binary<V: VariableBaseMSM>(mut bases: &[V::MulBase], mut scalars: &[bool]) -> V {
    let chunk_size = match preamble(&mut bases, &mut scalars) {
        Some(chunk_size) => chunk_size,
        None => return V::zero(),
    };

    // We only need to process the non-zero scalars.
    cfg_chunks!(bases, chunk_size)
        .zip(cfg_chunks!(scalars, chunk_size))
        .map(|(bases, scalars)| {
            let mut res = V::ZERO_BUCKET;
            for (base, _) in bases.iter().zip(scalars).filter(|(_, &s)| s) {
                res += base;
            }
            res.into()
        })
        .sum()
}

pub(super) fn msm_small<V: VariableBaseMSM, T: Into<u64> + Copy + Send + Sync>(
    mut bases: &[V::MulBase],
    mut scalars: &[T],
) -> V {
    let _chunk_size = match preamble(&mut bases, &mut scalars) {
        Some(chunk_size) => chunk_size,
        None => return V::zero(),
    };

    #[cfg(feature = "parallel")]
    let result = parallelization_helper(scalars, bases, _chunk_size, |b, s| {
        msm_small_serial::<V, _>(b, s)
    });

    #[cfg(not(feature = "parallel"))]
    let result = msm_small_serial::<V, _>(bases, scalars);
    result
}

fn compute_c(num_scalars: usize) -> usize {
    if num_scalars < 32 {
        3
    } else {
        ln_without_floats(num_scalars)
    }
}
