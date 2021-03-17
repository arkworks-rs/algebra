use ark_ff::prelude::*;
use ark_std::vec::Vec;

use crate::{AffineCurve, ProjectiveCurve};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub struct VariableBaseMSM;

impl VariableBaseMSM {
    pub fn multi_scalar_mul<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as PrimeField>::BigInt],
    ) -> G::Projective {
        let size = ark_std::cmp::min(bases.len(), scalars.len());
        let scalars = &scalars[..size];
        let bases = &bases[..size];
        let scalars_and_bases_iter = scalars.iter().zip(bases).filter(|(s, _)| !s.is_zero());

        let c = if size < 32 {
            3
        } else {
            super::ln_without_floats(size) + 2
        };

        let num_bits = <G::ScalarField as PrimeField>::Params::MODULUS_BITS as usize;
        let fr_one = G::ScalarField::one().into_repr();

        let zero = G::Projective::zero();
        let window_starts: Vec<_> = (0..num_bits).step_by(c).collect();

        // Each window is of size `c`.
        // We divide up the bits 0..num_bits into windows of size `c`, and
        // in parallel process each such window.
        let window_sums: Vec<_> = ark_std::cfg_into_iter!(window_starts)
            .map(|w_start| {
                let mut res = zero;
                // We don't need the "zero" bucket, so we only have 2^c - 1 buckets.
                let mut buckets = vec![zero; (1 << c) - 1];
                // This clone is cheap, because the iterator contains just a
                // pointer and an index into the original vectors.
                scalars_and_bases_iter.clone().for_each(|(&scalar, base)| {
                    if scalar == fr_one {
                        // We only process unit scalars once in the first window.
                        if w_start == 0 {
                            res.add_assign_mixed(base);
                        }
                    } else {
                        let mut scalar = scalar;

                        // We right-shift by w_start, thus getting rid of the
                        // lower bits.
                        scalar.divn(w_start as u32);

                        // We mod the remaining bits by 2^{window size}, thus taking `c` bits.
                        let scalar = scalar.as_ref()[0] % (1 << c);

                        // If the scalar is non-zero, we update the corresponding
                        // bucket.
                        // (Recall that `buckets` doesn't have a zero bucket.)
                        if scalar != 0 {
                            buckets[(scalar - 1) as usize].add_assign_mixed(base);
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
                let mut running_sum = G::Projective::zero();
                buckets.into_iter().rev().for_each(|b| {
                    running_sum += &b;
                    res += &running_sum;
                });
                res
            })
            .collect();

        // We store the sum for the lowest window.
        let lowest = *window_sums.first().unwrap();

        // We're traversing windows from high to low.
        lowest
            + &window_sums[1..]
                .iter()
                .rev()
                .fold(zero, |mut total, sum_i| {
                    total += sum_i;
                    for _ in 0..c {
                        total.double_in_place();
                    }
                    total
                })
    }

    pub fn multi_scalar_mul_batched<G: AffineCurve, BigInt: BigInteger>(
        bases: &[G],
        scalars: &[BigInt],
        num_bits: usize,
    ) -> G::Projective {
        let c = if scalars.len() < 32 {
            1
        } else {
            super::ln_without_floats(scalars.len()) + 2
        };

        let zero = G::Projective::zero();
        let window_starts: Vec<_> = (0..num_bits).step_by(c).collect();

        #[cfg(feature = "parallel")]
        let window_starts_iter = window_starts.into_par_iter();
        #[cfg(not(feature = "parallel"))]
        let window_starts_iter = window_starts.into_iter();

        // Each window is of size `c`.
        // We divide up the bits 0..num_bits into windows of size `c`, and
        // in parallel process each such window.
        let window_sums: Vec<_> = window_starts_iter
            .map(|w_start| {
                // We don't need the "zero" bucket, so we only have 2^c - 1 buckets
                let log2_n_bucket = if (w_start % c) != 0 { w_start % c } else { c };
                let n_buckets = (1 << log2_n_bucket) - 1;

                let _now = timer!();
                let mut bucket_positions: Vec<_> = scalars
                    .iter()
                    .enumerate()
                    .map(|(pos, &scalar)| {
                        let mut scalar = scalar;

                        // We right-shift by w_start, thus getting rid of the
                        // lower bits.
                        scalar.divn(w_start as u32);

                        // We mod the remaining bits by the window size.
                        let res = (scalar.as_ref()[0] % (1 << c)) as i32;
                        BucketPosition {
                            bucket: (res - 1) as u32,
                            position: pos as u32,
                        }
                    })
                    .collect();
                timer_println!(_now, "scalars->buckets");

                let _now = timer!();
                let buckets =
                    batch_bucketed_add::<G>(n_buckets, &bases[..], &mut bucket_positions[..]);
                timer_println!(_now, "bucket add");

                let _now = timer!();
                let mut res = zero;
                let mut running_sum = G::Projective::zero();
                for b in buckets.into_iter().rev() {
                    running_sum.add_assign_mixed(&b);
                    res += &running_sum;
                }
                timer_println!(_now, "accumulating sums");
                (res, log2_n_bucket)
            })
            .collect();

        // We store the sum for the lowest window.
        let lowest = window_sums.first().unwrap().0;

        // We're traversing windows from high to low.
        lowest
            + &window_sums[1..].iter().rev().fold(
                zero,
                |total: G::Projective, (sum_i, window_size): &(G::Projective, usize)| {
                    let mut total = total + sum_i;
                    for _ in 0..*window_size {
                        total.double_in_place();
                    }
                    total
                },
            )
    }
}
