use ark_ff::{prelude::*, PrimeField};
use ark_std::{borrow::Borrow, iterable::Iterable, ops::AddAssign, vec::Vec};

use crate::{AffineCurve, ProjectiveCurve};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub mod stream_pippenger;
pub use stream_pippenger::*;

pub struct VariableBase;

impl VariableBase {
    /// Optimized implementation of multi-scalar multiplication.
    ///
    /// Will return `None` if `bases` and `scalar` have different lengths.
    ///
    /// Reference: [`VariableBase::msm`]
    pub fn msm_checked_len<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as PrimeField>::BigInt],
    ) -> Option<G::Projective> {
        (bases.len() == scalars.len()).then(|| Self::msm(bases, scalars))
    }

    /// Optimized implementation of multi-scalar multiplication.
    ///
    /// Will multiply the tuples of the diagonal product of `bases × scalars`
    /// and sum the resulting set. Will iterate only for the elements of the
    /// smallest of the two sets, ignoring the remaining elements of the biggest
    /// set.
    ///
    /// ∑i (Bi · Si)
    pub fn msm<G: AffineCurve>(
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

        let num_bits = G::ScalarField::MODULUS_BIT_SIZE as usize;
        let fr_one = G::ScalarField::one().into_bigint();

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
    /// Streaming multi-scalar multiplication algorithm with hard-coded chunk
    /// size.
    pub fn msm_chunks<G, F, I: ?Sized, J>(bases_stream: &J, scalars_stream: &I) -> G::Projective
    where
        G: AffineCurve<ScalarField = F>,
        I: Iterable,
        F: PrimeField,
        I::Item: Borrow<F>,
        J: Iterable,
        J::Item: Borrow<G>,
    {
        assert!(scalars_stream.len() <= bases_stream.len());

        // remove offset
        let bases_init = bases_stream.iter();
        let mut scalars = scalars_stream.iter();

        // align the streams
        // TODO: change `skip` to `advance_by` once rust-lang/rust#7774 is fixed.
        // See <https://github.com/rust-lang/rust/issues/77404>
        let mut bases = bases_init.skip(bases_stream.len() - scalars_stream.len());
        let step: usize = 1 << 20;
        let mut result = G::Projective::zero();
        for _ in 0..(scalars_stream.len() + step - 1) / step {
            let bases_step = (&mut bases)
                .take(step)
                .map(|b| *b.borrow())
                .collect::<Vec<_>>();
            let scalars_step = (&mut scalars)
                .take(step)
                .map(|s| s.borrow().into_bigint())
                .collect::<Vec<_>>();
            result.add_assign(crate::msm::VariableBase::msm(
                bases_step.as_slice(),
                scalars_step.as_slice(),
            ));
        }
        result
    }
}
