use ark_ff::prelude::*;
use ark_std::{
    borrow::Borrow,
    cfg_chunks, cfg_into_iter, cfg_iter,
    iterable::Iterable,
    ops::{AddAssign, SubAssign},
    vec,
    vec::Vec,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub mod stream_pippenger;
pub use stream_pippenger::*;

use super::ScalarMul;

#[cfg(all(
    target_has_atomic = "8",
    target_has_atomic = "16",
    target_has_atomic = "32",
    target_has_atomic = "64",
    target_has_atomic = "ptr"
))]
type DefaultHasher = ahash::AHasher;

#[cfg(not(all(
    target_has_atomic = "8",
    target_has_atomic = "16",
    target_has_atomic = "32",
    target_has_atomic = "64",
    target_has_atomic = "ptr"
)))]
type DefaultHasher = fnv::FnvHasher;

pub trait VariableBaseMSM: ScalarMul + for<'a> AddAssign<&'a Self::Bucket> {
    type Bucket: Default
        + Copy
        + Clone
        + for<'a> AddAssign<&'a Self::Bucket>
        + for<'a> SubAssign<&'a Self::Bucket>
        + AddAssign<Self::MulBase>
        + SubAssign<Self::MulBase>
        + for<'a> AddAssign<&'a Self::MulBase>
        + for<'a> SubAssign<&'a Self::MulBase>
        + Send
        + Sync
        + Into<Self>;

    const ZERO_BUCKET: Self::Bucket;
    /// Computes an inner product between the [`PrimeField`] elements in `scalars`
    /// and the corresponding group elements in `bases`.
    ///
    /// If the elements have different length, it will chop the slices to the
    /// shortest length between `scalars.len()` and `bases.len()`.
    ///
    /// Reference: [`VariableBaseMSM::msm`]
    fn msm_unchecked(bases: &[Self::MulBase], scalars: &[Self::ScalarField]) -> Self {
        let bigints = cfg_into_iter!(scalars)
            .map(|s| s.into_bigint())
            .collect::<Vec<_>>();
        Self::msm_bigint(bases, bigints.as_slice())
    }

    /// Performs multi-scalar multiplication.
    ///
    /// # Warning
    ///
    /// This method checks that `bases` and `scalars` have the same length.
    /// If they are unequal, it returns an error containing
    /// the shortest length over which the MSM can be performed.
    fn msm(bases: &[Self::MulBase], scalars: &[Self::ScalarField]) -> Result<Self, usize> {
        (bases.len() == scalars.len())
            .then(|| Self::msm_unchecked(bases, scalars))
            .ok_or_else(|| bases.len().min(scalars.len()))
    }

    /// Optimized implementation of multi-scalar multiplication.
    fn msm_bigint(
        bases: &[Self::MulBase],
        bigints: &[<Self::ScalarField as PrimeField>::BigInt],
    ) -> Self {
        if Self::NEGATION_IS_CHEAP {
            msm_signed(bases, bigints)
        } else {
            msm_unsigned(bases, bigints)
        }
    }

    /// Performs multi-scalar multiplication when the scalars are known to be boolean.
    /// The default implementation is faster than [`Self::msm_bigint`].
    fn msm_u1(bases: &[Self::MulBase], scalars: &[bool]) -> Self {
        msm_binary(bases, scalars)
    }

    /// Performs multi-scalar multiplication when the scalars are known to be `u8`-sized.
    /// The default implementation is faster than [`Self::msm_bigint`].
    fn msm_u8(bases: &[Self::MulBase], scalars: &[u8]) -> Self {
        msm_u8(bases, scalars)
    }

    /// Performs multi-scalar multiplication when the scalars are known to be `u16`-sized.
    /// The default implementation is faster than [`Self::msm_bigint`].
    fn msm_u16(bases: &[Self::MulBase], scalars: &[u16]) -> Self {
        msm_u16(bases, scalars)
    }

    /// Performs multi-scalar multiplication when the scalars are known to be `u32`-sized.
    /// The default implementation is faster than [`Self::msm_bigint`].
    fn msm_u32(bases: &[Self::MulBase], scalars: &[u32]) -> Self {
        msm_u32(bases, scalars)
    }

    /// Performs multi-scalar multiplication when the scalars are known to be `u64`-sized.
    /// The default implementation is faster than [`Self::msm_bigint`].
    fn msm_u64(bases: &[Self::MulBase], scalars: &[u64]) -> Self {
        msm_u64(bases, scalars)
    }

    /// Streaming multi-scalar multiplication algorithm with hard-coded chunk
    /// size.
    fn msm_chunks<I, J>(bases_stream: &J, scalars_stream: &I) -> Self
    where
        I: Iterable + ?Sized,
        I::Item: Borrow<Self::ScalarField>,
        J: Iterable,
        J::Item: Borrow<Self::MulBase>,
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
        let mut result = Self::zero();
        for _ in 0..scalars_stream.len().div_ceil(step) {
            let bases_step = (&mut bases)
                .take(step)
                .map(|b| *b.borrow())
                .collect::<Vec<_>>();
            let scalars_step = (&mut scalars)
                .take(step)
                .map(|s| s.borrow().into_bigint())
                .collect::<Vec<_>>();
            result += Self::msm_bigint(bases_step.as_slice(), scalars_step.as_slice());
        }
        result
    }
}

#[inline]
fn get_group<const N: usize, A: Send + Sync, B: Send + Sync>(
    grouped: &[u64],
    f: impl Fn(usize) -> (A, B) + Send + Sync,
) -> (Vec<A>, Vec<B>) {
    let extract_index = |i| ((i << N) >> N) as usize;
    cfg_iter!(grouped)
        .map(|&i| f(extract_index(i)))
        .unzip::<_, _, Vec<_>, Vec<_>>()
}

#[inline]
fn uget_group<A: Send + Sync, B: Send + Sync>(
    grouped: &[u64],
    f: impl Fn(usize) -> (A, B) + Send + Sync,
) -> (Vec<A>, Vec<B>) {
    get_group::<3, _, _>(grouped, f)
}

#[inline]
fn iget_group<A: Send + Sync, B: Send + Sync>(
    grouped: &[u64],
    f: impl Fn(usize) -> (A, B) + Send + Sync,
) -> (Vec<A>, Vec<B>) {
    get_group::<4, _, _>(grouped, f)
}

/// Computes multi-scalar multiplication where the scalars
/// are positive.
/// Should be used when the negation is expensive, i.e. when
/// `V::NEGATION_IS_CHEAP` is `false`.
fn msm_unsigned<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    scalars: &[<V::ScalarField as PrimeField>::BigInt],
) -> V {
    // Partition scalars according to whether
    // 1. they are in the range {0, 1};
    // 3. they are in the range [0, 255];
    // 4. they are small-sized (< 16 bits);
    // 4. they are intermediate-sized (< 32 bits);
    // 6. they are medium-sized (< 64 bits);
    // 7. the rest.

    let size = bases.len().min(scalars.len());
    let bases = &bases[..size];
    let scalars = &scalars[..size];

    let mut grouped = cfg_iter!(scalars)
        .enumerate()
        .filter(|(_, scalar)| !scalar.is_zero())
        .map(|(i, scalar)| {
            let num_bits = scalar.num_bits();
            let group = if num_bits <= 1 {
                1u8
            } else if num_bits <= 8 {
                3u8
            } else if num_bits <= 16 {
                4u8
            } else if num_bits <= 32 {
                5u8
            } else if num_bits <= 64 {
                6u8
            } else {
                7u8
            };
            // group is at most 7, so we can fit it in 3 bits.
            (i as u64) ^ ((group as u64) << 61)
        })
        .collect::<Vec<_>>();
    let extract_group = |i| (i >> 61) as u8;
    #[cfg(feature = "parallel")]
    grouped.par_sort_unstable_by_key(|i| extract_group(*i));
    #[cfg(not(feature = "parallel"))]
    grouped.sort_unstable_by_key(|i| extract_group(*i));

    let s1 = 0;
    let s3 = s1 + grouped[s1..].partition_point(|i| extract_group(*i) < 3);
    let s4 = s3 + grouped[s3..].partition_point(|i| extract_group(*i) < 4);
    let s5 = s4 + grouped[s4..].partition_point(|i| extract_group(*i) < 5);
    let s6 = s5 + grouped[s5..].partition_point(|i| extract_group(*i) < 6);
    let s7 = s6 + grouped[s6..].partition_point(|i| extract_group(*i) < 7);

    let (b1, s1) = uget_group(&grouped[s1..s3], |i| {
        (bases[i], scalars[i].as_ref()[0] == 1)
    });
    let (b3, s3) = uget_group(&grouped[s3..s4], |i| {
        (bases[i], scalars[i].as_ref()[0] as u8)
    });
    let (b4, s4) = uget_group(&grouped[s4..s5], |i| {
        (bases[i], scalars[i].as_ref()[0] as u16)
    });
    let (b5, s5) = uget_group(&grouped[s5..s6], |i| {
        (bases[i], scalars[i].as_ref()[0] as u32)
    });
    let (b6, s6) = uget_group(&grouped[s6..s7], |i| {
        (bases[i], scalars[i].as_ref()[0] as u64)
    });
    let (b7, s7) = uget_group(&grouped[s7..], |i| (bases[i], scalars[i]));

    let result: V = msm_binary::<V>(&b1, &s1)
        + msm_u8::<V>(&b3, &s3)
        + msm_u16::<V>(&b4, &s4)
        + msm_u32::<V>(&b5, &s5)
        + msm_u64::<V>(&b6, &s6)
        + msm_bigint::<V>(&b7, &s7, V::ScalarField::MODULUS_BIT_SIZE as usize);
    result.into()
}

#[inline(always)]
fn sub<B: BigInteger>(m: &B, scalar: &B) -> u64 {
    let mut negated = *m;
    negated.sub_with_borrow(scalar);
    negated.as_ref()[0]
}

/// Computes multi-scalar multiplication where the scalars
/// can be negative, zero, or positive.
/// Should be used when the negation is cheap, i.e. when
/// `V::NEGATION_IS_CHEAP` is `true`.
fn msm_signed<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    scalars: &[<V::ScalarField as PrimeField>::BigInt],
) -> V {
    // Partition scalars according to whether
    // 1. they are in the range {-1, 0, 1};
    // 2. they are in the range [-127, 127];
    // 3. they are in the range [0, 255];
    // 4. they are small-sized (< 16 bits);
    // 4. they are intermediate-sized (< 32 bits);
    // 6. they are medium-sized (< 64 bits);
    // 7. the rest.

    let size = bases.len().min(scalars.len());
    let bases = &bases[..size];
    let scalars = &scalars[..size];

    let mut grouped = cfg_iter!(scalars)
        .enumerate()
        .filter(|(_, scalar)| !scalar.is_zero())
        .map(|(i, scalar)| {
            let mut p_minus_scalar = V::ScalarField::MODULUS;
            p_minus_scalar.sub_with_borrow(scalar);
            let num_bits = scalar.num_bits();
            let neg_num_bits = p_minus_scalar.num_bits();
            let group = if num_bits <= 1 {
                0u8
            } else if neg_num_bits <= 1 {
                1u8
            } else if num_bits <= 8 {
                2u8
            } else if neg_num_bits <= 8 {
                3u8
            } else if num_bits <= 16 {
                4u8
            } else if neg_num_bits <= 16 {
                5u8
            } else if num_bits <= 32 {
                6u8
            } else if neg_num_bits <= 32 {
                7u8
            } else if num_bits <= 64 {
                8u8
            } else if neg_num_bits <= 64 {
                9u8
            } else {
                10u8
            };
            // group is at most 10, so we can fit it in 4 bits.
            // hence, we can use the first 60 bits for the index,
            // and the last 4 bits for the group.
            (((i as u64) << 4) >> 4) ^ ((group as u64) << 60)
        })
        .collect::<Vec<_>>();
    let extract_group = |i| (i >> 60) as u8;

    #[cfg(feature = "parallel")]
    grouped.par_sort_unstable_by_key(|i| extract_group(*i));
    #[cfg(not(feature = "parallel"))]
    grouped.sort_unstable_by_key(|i| extract_group(*i));

    let su1 = 0;
    let si1 = su1 + grouped[su1..].partition_point(|i| extract_group(*i) < 1);
    let su8 = si1 + grouped[si1..].partition_point(|i| extract_group(*i) < 2);
    let si8 = su8 + grouped[su8..].partition_point(|i| extract_group(*i) < 3);
    let su16 = si8 + grouped[si8..].partition_point(|i| extract_group(*i) < 4);
    let si16 = su16 + grouped[su16..].partition_point(|i| extract_group(*i) < 5);
    let su32 = si16 + grouped[si16..].partition_point(|i| extract_group(*i) < 6);
    let si32 = su32 + grouped[su32..].partition_point(|i| extract_group(*i) < 7);
    let su64 = si32 + grouped[si32..].partition_point(|i| extract_group(*i) < 8);
    let si64 = su64 + grouped[su64..].partition_point(|i| extract_group(*i) < 9);
    let sf = si64 + grouped[si64..].partition_point(|i| extract_group(*i) < 10);

    let m = V::ScalarField::MODULUS;
    let mut result: V;

    // Handle the scalars in the range {-1, 0, 1}.
    let (ub, us) = iget_group(&grouped[su1..si1], |i| {
        (bases[i], scalars[i].as_ref()[0] == 1)
    });
    let (ib, is) = iget_group(&grouped[si1..su8], |i| {
        (bases[i], sub(&m, &scalars[i]) == 1)
    });
    result = msm_binary::<V>(&ub, &us) - msm_binary::<V>(&ib, &is);

    // Handle positive and negative u8 scalars.
    let (ub, us) = iget_group(&grouped[su8..si8], |i| {
        (bases[i], scalars[i].as_ref()[0] as u8)
    });
    let (ib, is) = iget_group(&grouped[si8..su16], |i| {
        (bases[i], sub(&m, &scalars[i]) as u8)
    });
    result += msm_u8::<V>(&ub, &us) - msm_u8::<V>(&ib, &is);

    // Handle positive and negative u16 scalars.
    let (ub, us) = iget_group(&grouped[su16..si16], |i| {
        (bases[i], scalars[i].as_ref()[0] as u16)
    });
    let (ib, is) = iget_group(&grouped[si16..su32], |i| {
        (bases[i], sub(&m, &scalars[i]) as u16)
    });
    result += msm_u16::<V>(&ub, &us) - msm_u16::<V>(&ib, &is);

    // Handle positive and negative u32 scalars.
    let (ub, us) = iget_group(&grouped[su32..si32], |i| {
        (bases[i], scalars[i].as_ref()[0] as u32)
    });
    let (ib, is) = iget_group(&grouped[si32..su64], |i| {
        (bases[i], sub(&m, &scalars[i]) as u32)
    });
    result += msm_u32::<V>(&ub, &us) - msm_u32::<V>(&ib, &is);

    // Handle positive and negative u64 scalars.
    let (ub, us) = iget_group(&grouped[su64..si64], |i| (bases[i], scalars[i].as_ref()[0]));
    let (ib, is) = iget_group(&grouped[si64..sf], |i| (bases[i], sub(&m, &scalars[i])));
    result += msm_u64::<V>(&ub, &us) - msm_u64::<V>(&ib, &is);

    // Handle the rest of the scalars.
    let (bf, sf) = iget_group(&grouped[sf..], |i| (bases[i], scalars[i]));
    result += msm_bigint_wnaf::<V>(&bf, &sf);

    result.into()
}

fn preamble<A, B>(bases: &mut &[A], scalars: &mut &[B]) -> Option<usize> {
    let size = bases.len().min(scalars.len());
    if size == 0 {
        return None;
    }
    #[cfg(feature = "parallel")]
    let chunk_size = {
        let chunk_size = size / rayon::current_num_threads();
        if chunk_size == 0 {
            size
        } else {
            chunk_size
        }
    };
    #[cfg(not(feature = "parallel"))]
    let chunk_size = size;

    *bases = &bases[..size];
    *scalars = &scalars[..size];
    Some(chunk_size)
}

/// Computes multi-scalar multiplication where the scalars
/// lie in the range {-1, 0, 1}.
fn msm_binary<V: VariableBaseMSM>(mut bases: &[V::MulBase], mut scalars: &[bool]) -> V {
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

fn msm_u8<V: VariableBaseMSM>(mut bases: &[V::MulBase], mut scalars: &[u8]) -> V {
    let chunk_size = match preamble(&mut bases, &mut scalars) {
        Some(chunk_size) => chunk_size,
        None => return V::zero(),
    };
    cfg_chunks!(bases, chunk_size)
        .zip(cfg_chunks!(scalars, chunk_size))
        .map(|(bases, scalars)| msm_serial::<V>(bases, scalars))
        .sum()
}

fn msm_u16<V: VariableBaseMSM>(mut bases: &[V::MulBase], mut scalars: &[u16]) -> V {
    let chunk_size = match preamble(&mut bases, &mut scalars) {
        Some(chunk_size) => chunk_size,
        None => return V::zero(),
    };
    cfg_chunks!(bases, chunk_size)
        .zip(cfg_chunks!(scalars, chunk_size))
        .map(|(bases, scalars)| msm_serial::<V>(bases, scalars))
        .sum()
}

fn msm_u32<V: VariableBaseMSM>(mut bases: &[V::MulBase], mut scalars: &[u32]) -> V {
    let chunk_size = match preamble(&mut bases, &mut scalars) {
        Some(chunk_size) => chunk_size,
        None => return V::zero(),
    };
    cfg_chunks!(bases, chunk_size)
        .zip(cfg_chunks!(scalars, chunk_size))
        .map(|(bases, scalars)| msm_serial::<V>(bases, scalars))
        .sum()
}

fn msm_u64<V: VariableBaseMSM>(mut bases: &[V::MulBase], mut scalars: &[u64]) -> V {
    let chunk_size = match preamble(&mut bases, &mut scalars) {
        Some(chunk_size) => chunk_size,
        None => return V::zero(),
    };
    cfg_chunks!(bases, chunk_size)
        .zip(cfg_chunks!(scalars, chunk_size))
        .map(|(bases, scalars)| msm_serial::<V>(bases, scalars))
        .sum()
}

// Compute msm using windowed non-adjacent form
fn msm_bigint_wnaf_parallel<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    bigints: &[<V::ScalarField as PrimeField>::BigInt],
) -> V {
    let size = bases.len().min(bigints.len());
    let scalars = &bigints[..size];
    let bases = &bases[..size];

    let c = if size < 32 {
        3
    } else {
        super::ln_without_floats(size) + 2
    };

    let num_bits = V::ScalarField::MODULUS_BIT_SIZE as usize;
    let digits_count = num_bits.div_ceil(c);
    #[cfg(feature = "parallel")]
    let scalar_digits = scalars
        .into_par_iter()
        .flat_map_iter(|s| make_digits(s, c, num_bits))
        .collect::<Vec<_>>();
    #[cfg(not(feature = "parallel"))]
    let scalar_digits = scalars
        .iter()
        .flat_map(|s| make_digits(s, c, num_bits))
        .collect::<Vec<_>>();
    let zero = V::ZERO_BUCKET;
    let window_sums: Vec<_> = ark_std::cfg_into_iter!(0..digits_count)
        .map(|i| {
            let mut buckets = vec![zero; 1 << c];
            for (digits, base) in scalar_digits.chunks(digits_count).zip(bases) {
                use ark_std::cmp::Ordering;
                // digits is the digits thing of the first scalar?
                let scalar = digits[i];
                match 0.cmp(&scalar) {
                    Ordering::Less => buckets[(scalar - 1) as usize] += base,
                    Ordering::Greater => buckets[(-scalar - 1) as usize] -= base,
                    Ordering::Equal => (),
                }
            }

            // prefix sum
            let mut running_sum = V::ZERO_BUCKET;
            let mut res = V::ZERO_BUCKET;
            buckets.into_iter().rev().for_each(|b| {
                running_sum += &b;
                res += &running_sum;
            });
            res
        })
        .collect();

    // We store the sum for the lowest window.
    let lowest: V = (*window_sums.first().unwrap()).into();

    // We're traversing windows from high to low.
    lowest
        + (&window_sums[1..])
            .iter()
            .rev()
            .fold(V::zero(), |mut total, sum_i| {
                total += sum_i;
                for _ in 0..c {
                    total.double_in_place();
                }
                total
            })
}

#[cfg(feature = "parallel")]
const THREADS_PER_CHUNK: usize = 2;

/// Computes an MSM using the windowed non-adjacent form (WNAF) algorithm.
/// To improve parallelism, when number of threads is at least 2, this
/// function will split the input into enough chunks so that each chunk
/// can be processed with 2 threads.
fn msm_bigint_wnaf<V: VariableBaseMSM>(
    mut bases: &[V::MulBase],
    mut scalars: &[<V::ScalarField as PrimeField>::BigInt],
) -> V {
    let size = bases.len().min(scalars.len());
    if size == 0 {
        return V::zero();
    }

    #[cfg(feature = "parallel")]
    let chunk_size = {
        let cur_num_threads = rayon::current_num_threads();
        let num_chunks = if cur_num_threads < THREADS_PER_CHUNK {
            1
        } else {
            cur_num_threads / THREADS_PER_CHUNK
        };
        let chunk_size = size / num_chunks;
        if chunk_size == 0 {
            size
        } else {
            chunk_size
        }
    };
    #[cfg(not(feature = "parallel"))]
    let chunk_size = size;

    bases = &bases[..size];
    scalars = &scalars[..size];

    cfg_chunks!(bases, chunk_size)
        .zip(cfg_chunks!(scalars, chunk_size))
        .map(|(bases, scalars)| {
            #[cfg(feature = "parallel")]
            let result = rayon::ThreadPoolBuilder::new()
                .num_threads(THREADS_PER_CHUNK.min(rayon::current_num_threads()))
                .build()
                .unwrap()
                .install(|| msm_bigint_wnaf_parallel::<V>(bases, scalars));

            #[cfg(not(feature = "parallel"))]
            let result = msm_bigint_wnaf_parallel::<V>(bases, scalars);

            result
        })
        .sum()
}

/// Optimized implementation of multi-scalar multiplication.
fn msm_bigint<V: VariableBaseMSM>(
    mut bases: &[V::MulBase],
    mut scalars: &[<V::ScalarField as PrimeField>::BigInt],
    num_bits: usize,
) -> V {
    if preamble(&mut bases, &mut scalars).is_none() {
        return V::zero();
    }
    let size = scalars.len();
    let scalars_and_bases_iter = scalars.iter().zip(bases).filter(|(s, _)| !s.is_zero());

    let c = if size < 32 {
        3
    } else {
        super::ln_without_floats(size) + 2
    };

    let one = V::ScalarField::one().into_bigint();

    let zero = V::ZERO_BUCKET;

    // Each window is of size `c`.
    // We divide up the bits 0..num_bits into windows of size `c`, and
    // in parallel process each such window.
    let window_sums: Vec<_> = ark_std::cfg_into_iter!(0..num_bits)
        .step_by(c)
        .map(|w_start| {
            let mut res = zero;
            // We don't need the "zero" bucket, so we only have 2^c - 1 buckets.
            let mut buckets = vec![zero; (1 << c) - 1];
            // This clone is cheap, because the iterator contains just a
            // pointer and an index into the original vectors.
            scalars_and_bases_iter.clone().for_each(|(&scalar, base)| {
                if scalar == one {
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
                    let scalar = scalar.as_ref()[0] % (1 << c);

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

    // We store the sum for the lowest window.
    let lowest = window_sums.first().copied().map_or(V::ZERO, Into::into);

    // We're traversing windows from high to low.
    lowest
        + &window_sums[1..]
            .iter()
            .rev()
            .fold(V::zero(), |mut total, sum_i| {
                total += sum_i;
                for _ in 0..c {
                    total.double_in_place();
                }
                total
            })
}

fn msm_serial<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    scalars: &[impl Into<u64> + Copy + Send + Sync],
) -> V {
    let c = if bases.len() < 32 {
        3
    } else {
        super::ln_without_floats(bases.len()) + 2
    };

    let zero = V::ZERO_BUCKET;

    // Each window is of size `c`.
    // We divide up the bits 0..num_bits into windows of size `c`, and
    // in parallel process each such window.
    let two_to_c = 1 << c;
    let window_sums: Vec<_> = (0..(core::mem::size_of::<u64>() * 8))
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

    // We store the sum for the lowest window.
    let lowest = window_sums.first().copied().map_or(V::ZERO, Into::into);

    // We're traversing windows from high to low.
    lowest
        + &window_sums[1..]
            .iter()
            .rev()
            .fold(V::zero(), |mut total, sum_i| {
                total += sum_i;
                for _ in 0..c {
                    total.double_in_place();
                }
                total
            })
}

// From: https://github.com/arkworks-rs/gemini/blob/main/src/kzg/msm/variable_base.rs#L20
fn make_digits(a: &impl BigInteger, w: usize, num_bits: usize) -> impl Iterator<Item = i64> + '_ {
    let scalar = a.as_ref();
    let radix: u64 = 1 << w;
    let window_mask: u64 = radix - 1;

    let mut carry = 0u64;
    let num_bits = if num_bits == 0 {
        a.num_bits() as usize
    } else {
        num_bits
    };
    let digits_count = num_bits.div_ceil(w);

    (0..digits_count).map(move |i| {
        // Construct a buffer of bits of the scalar, starting at `bit_offset`.
        let bit_offset = i * w;
        let u64_idx = bit_offset / 64;
        let bit_idx = bit_offset % 64;
        // Read the bits from the scalar
        let bit_buf = if bit_idx < 64 - w || u64_idx == scalar.len() - 1 {
            // This window's bits are contained in a single u64,
            // or it's the last u64 anyway.
            scalar[u64_idx] >> bit_idx
        } else {
            // Combine the current u64's bits with the bits from the next u64
            (scalar[u64_idx] >> bit_idx) | (scalar[1 + u64_idx] << (64 - bit_idx))
        };

        // Read the actual coefficient value from the window
        let coef = carry + (bit_buf & window_mask); // coef = [0, 2^r)

        // Recenter coefficients from [0,2^w) to [-2^w/2, 2^w/2)
        carry = (coef + radix / 2) >> w;
        let mut digit = (coef as i64) - (carry << w) as i64;

        if i == digits_count - 1 {
            digit += (carry << w) as i64;
        }
        digit
    })
}
