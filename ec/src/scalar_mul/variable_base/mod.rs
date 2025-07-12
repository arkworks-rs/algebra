use ark_ff::prelude::*;
use ark_std::{
    borrow::Borrow,
    cfg_chunks, cfg_chunks_mut, cfg_into_iter, cfg_iter,
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
        msm_signed(bases, bigints)
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
fn large_value_unzip<A: Send + Sync, B: Send + Sync>(
    grouped: &[PackedIndex],
    f: impl Fn(usize) -> (A, B) + Send + Sync,
) -> (Vec<A>, Vec<B>) {
    cfg_iter!(grouped)
        .map(|&i| f(i.index()))
        .unzip::<_, _, Vec<_>, Vec<_>>()
}

#[inline]
fn small_value_unzip<A: Send + Sync, B: Send + Sync>(
    grouped: &[PackedIndex],
    f: impl Fn(usize, u16) -> (A, B) + Send + Sync,
) -> (Vec<A>, Vec<B>) {
    cfg_iter!(grouped)
        .map(|&i| (f(i.index(), i.value())))
        .unzip::<_, _, Vec<_>, Vec<_>>()
}

#[inline(always)]
fn sub<B: BigInteger>(m: &B, scalar: &B) -> u64 {
    let mut negated = *m;
    negated.sub_with_borrow(scalar);
    negated.as_ref()[0]
}

// 44 zeroes, 1 in the next 16 bits, 0 rest
const VALUE_MASK: u64 = (u16::MAX as u64) << 44;

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScalarSize {
    U1 = 0,
    NegU1 = 1,
    U8 = 2,
    NegU8 = 3,
    U16 = 4,
    NegU16 = 5,
    U32 = 6,
    NegU32 = 7,
    U64 = 8,
    NegU64 = 9,
    BigInt = 10,
}

impl ScalarSize {
    #[inline]
    fn partition_point(self, v: &[PackedIndex]) -> usize {
        v.partition_point(|i| i.group() < self as u8 + 1)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct PackedIndex(pub u64);

impl PackedIndex {
    #[inline(always)]
    const fn new(index: usize, group: ScalarSize, value: u16) -> Self {
        // Pack the index, group, and value into a single u64.
        let index_bits = ((index as u64) << 20) >> 20;
        let group_bits = (group as u64) << 60;
        let value_bits = (value as u64) << 44;

        Self(index_bits | value_bits | group_bits)
    }
    /// Extracts the index from the packed value.
    #[inline(always)]
    const fn index(self) -> usize {
        ((self.0 << 20) >> 20) as usize
    }

    /// Extracts the group from the packed value.
    #[inline(always)]
    const fn group(self) -> u8 {
        (self.0 >> 60) as u8
    }

    #[inline(always)]
    const fn value(self) -> u16 {
        ((self.0 & VALUE_MASK) >> 44) as u16
    }
}

/// Computes multi-scalar multiplication where the scalars
/// can be negative, zero, or positive.
/// Should be used when the negation is cheap, i.e. when
/// `V::NEGATION_IS_CHEAP` is `true`.
fn msm_signed<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    scalars: &[<V::ScalarField as PrimeField>::BigInt],
) -> V {
    let size = bases.len().min(scalars.len());
    let bases = &bases[..size];
    let scalars = &scalars[..size];

    // Partition scalars according to their size.
    let mut grouped = cfg_iter!(scalars)
        .enumerate()
        .filter(|(_, scalar)| !scalar.is_zero())
        .map(|(i, scalar)| {
            use ScalarSize::*;
            let mut value = 0;
            let group = match scalar.num_bits() {
                0..=1 => U1,
                2..=8 => U8,
                9..=16 => U16,
                17..=32 => U32,
                33..=64 => U64,
                _ => {
                    let mut p_minus_scalar = V::ScalarField::MODULUS;
                    p_minus_scalar.sub_with_borrow(scalar);
                    let group = match p_minus_scalar.num_bits() {
                        0..=1 => NegU1,
                        2..=8 => NegU8,
                        9..=16 => NegU16,
                        17..=32 => NegU32,
                        33..=64 => NegU64,
                        _ => ScalarSize::BigInt,
                    };
                    if matches!(group, NegU1 | NegU8 | NegU16) {
                        value = p_minus_scalar.as_ref()[0] as u16
                    }
                    group
                },
            };
            if matches!(group, U1 | U8 | U16) {
                value = (scalar.as_ref()[0]) as u16;
            };
            PackedIndex::new(i, group, value)
        })
        .collect::<Vec<_>>();

    #[cfg(feature = "parallel")]
    grouped.par_sort_unstable_by_key(|i| i.group());
    #[cfg(not(feature = "parallel"))]
    grouped.sort_unstable_by_key(|i| i.group());

    let (u1s, rest) = grouped.split_at(ScalarSize::U1.partition_point(&grouped));
    let (i1s, rest) = rest.split_at(ScalarSize::NegU1.partition_point(rest));
    let (u8s, rest) = rest.split_at(ScalarSize::U8.partition_point(rest));
    let (i8s, rest) = rest.split_at(ScalarSize::NegU8.partition_point(rest));
    let (u16s, rest) = rest.split_at(ScalarSize::U16.partition_point(rest));
    let (i16s, rest) = rest.split_at(ScalarSize::NegU16.partition_point(rest));
    let (u32s, rest) = rest.split_at(ScalarSize::U32.partition_point(rest));
    let (i32s, rest) = rest.split_at(ScalarSize::NegU32.partition_point(rest));
    let (u64s, rest) = rest.split_at(ScalarSize::U64.partition_point(rest));
    let (i64s, rest) = rest.split_at(ScalarSize::NegU64.partition_point(rest));
    let (bigints, _) = rest.split_at(ScalarSize::BigInt.partition_point(rest));

    let m = V::ScalarField::MODULUS;
    let mut add_result: V;
    let mut sub_result: V;

    // Handle the scalars in the range {-1, 0, 1}.
    let (ub, us) = small_value_unzip(u1s, |i, v| (bases[i], v == 1));
    let (ib, is) = small_value_unzip(i1s, |i, v| (bases[i], v == 1));
    add_result = msm_binary::<V>(&ub, &us);
    sub_result = msm_binary::<V>(&ib, &is);

    // Handle positive and negative u8 scalars.
    let (ub, us) = small_value_unzip(u8s, |i, v| (bases[i], v as u8));
    let (ib, is) = small_value_unzip(i8s, |i, v| (bases[i], v as u8));
    add_result += msm_u8::<V>(&ub, &us);
    sub_result += msm_u8::<V>(&ib, &is);

    // Handle positive and negative u16 scalars.
    let (ub, us) = small_value_unzip(u16s, |i, v| (bases[i], v as u16));
    let (ib, is) = small_value_unzip(i16s, |i, v| (bases[i], v as u16));
    add_result += msm_u16::<V>(&ub, &us);
    sub_result += msm_u16::<V>(&ib, &is);

    // Handle positive and negative u32 scalars.
    let (ub, us) = large_value_unzip(u32s, |i| (bases[i], scalars[i].as_ref()[0] as u32));
    let (ib, is) = large_value_unzip(i32s, |i| (bases[i], sub(&m, &scalars[i]) as u32));
    add_result += msm_u32::<V>(&ub, &us);
    sub_result += msm_u32::<V>(&ib, &is);

    // Handle positive and negative u64 scalars.
    let (ub, us) = large_value_unzip(u64s, |i| (bases[i], scalars[i].as_ref()[0]));
    let (ib, is) = large_value_unzip(i64s, |i| (bases[i], sub(&m, &scalars[i])));
    add_result += msm_u64::<V>(&ub, &us);
    sub_result += msm_u64::<V>(&ib, &is);

    // Handle the rest of the scalars.
    let (bf, mut sf) = large_value_unzip(bigints, |i| (bases[i], scalars[i]));
    if V::NEGATION_IS_CHEAP {
        add_result += msm_bigint_wnaf::<V>(&bf, &mut sf);
    } else {
        add_result += msm_bigint::<V>(&bf, &sf);
    }

    add_result - sub_result
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
    bigints: &mut [<V::ScalarField as PrimeField>::BigInt],
) -> V {
    let size = bases.len().min(bigints.len());
    let scalars = &mut bigints[..size];
    let bases = &bases[..size];

    let c = if size < 32 {
        3
    } else {
        super::ln_without_floats(size) + 2
    };

    let num_bits = V::ScalarField::MODULUS_BIT_SIZE as usize;
    let digits_count = num_bits.div_ceil(c);
    process_digits(scalars, c, num_bits);
    let digits_info = (0..digits_count)
        .map(|i| DigitInfo::new(i, c, scalars.len()))
        .collect::<Vec<_>>();

    let zero = V::ZERO_BUCKET;

    let mut window_sums = vec![V::zero(); digits_count];

    let window_mask = (1 << c) - 1;
    let sign_mask = 1 << (c - 1);
    let process_digit = |i: usize, out: &mut V| {
        let mut buckets = if i == digits_count - 1 {
            // No borrow for the last digit
            let final_size = num_bits - (digits_count - 1) * c;
            vec![V::ZERO_BUCKET; 1 << final_size]
        } else {
            vec![V::ZERO_BUCKET; 1 << (c - 1)]
        };
        let digit_info = &digits_info[i];
        let u64_idx = digit_info.u64_idx() as usize;
        let bit_idx = digit_info.bit_idx();
        let is_single_word = digit_info.is_single_word();

        for (scalar, base) in scalars.iter().zip(bases) {
            let scalar = scalar.as_ref();
            let coeff = read_digit(u64_idx, bit_idx, is_single_word, scalar, window_mask);

            if i == digits_count - 1 {
                let coef = scalar[u64_idx] >> bit_idx;
                if coef != 0 {
                    buckets[(coef - 1) as usize] += base;
                }
                continue;
            }

            if coeff == 0 {
                continue;
            }

            if coeff & sign_mask == 0 {
                buckets[(coeff - 1) as usize] += base;
            } else {
                buckets[(coeff & (!sign_mask)) as usize] -= base;
            }
        }

        let mut running_sum = zero;
        *out = V::zero();
        buckets.into_iter().rev().for_each(|b| {
            running_sum += &b;
            *out += &running_sum;
        });
    };

    // The original code uses rayon. Unfortunately, experiments have shown that
    // rayon does quite sub-optimally for this particular instance, and directly
    // spawning threads was faster.
    #[cfg(feature = "parallel")]
    rayon::scope(|s| {
        let len = window_sums.len();
        for (i, out) in window_sums.iter_mut().enumerate() {
            if i == len - 1 {
                process_digit(i, out);
            } else {
                s.spawn(move |_| {
                    process_digit(i, out);
                });
            }
        }
    });

    #[cfg(not(feature = "parallel"))]
    for (i, out) in window_sums.iter_mut().enumerate() {
        process_digit(i, out);
    }

    // We store the sum for the highest window.
    let mut total = *window_sums.last().unwrap();
    for i in (0..(window_sums.len() - 1)).rev() {
        for _ in 0..c {
            total.double_in_place();
        }
        total += &window_sums[i];
    }

    total
}

#[cfg(feature = "parallel")]
const THREADS_PER_CHUNK: usize = 2;

/// Computes an MSM using the windowed non-adjacent form (WNAF) algorithm.
/// To improve parallelism, when number of threads is at least 2, this
/// function will split the input into enough chunks so that each chunk
/// can be processed with 2 threads.
fn msm_bigint_wnaf<V: VariableBaseMSM>(
    mut bases: &[V::MulBase],
    mut scalars: &mut [<V::ScalarField as PrimeField>::BigInt],
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
    scalars = &mut scalars[..size];

    cfg_chunks!(bases, chunk_size)
        .zip(cfg_chunks_mut!(scalars, chunk_size))
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
    let num_bits = V::ScalarField::MODULUS_BIT_SIZE as usize;

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

// Assumes that `a` contains elements in the range [0, BigInt::MAX - 1].
// This allows the last digit to be processed without special handling.
fn process_digits(a: &mut [impl BigInteger], w: usize, num_bits: usize) {
    let radix: u64 = 1 << w;
    let window_mask: u64 = radix - 1;
    // The number of digits in the `radix`-ary representation
    // of the scalar.
    let num_digits = num_bits.div_ceil(w);

    let sign_mask: u64 = 1 << (w - 1);

    let digit_infos = (0..num_digits)
        .map(|i| DigitInfo::new(i, w, a[0].as_ref().len()))
        .collect::<Vec<_>>();

    ark_std::cfg_iter_mut!(a).for_each(|scalar| {
        let scalar = scalar.as_mut();

        let mut carry = 0u64;
        for digit_info in &digit_infos {
            modify_digit(scalar, &digit_info, w as u8, window_mask, |mut coeff| {
                // Add the carry from the previous digit to the current digit.
                coeff += carry;

                // The next two steps recenter coeff from [0,2^w) to [-2^w/2, 2^w/2)

                // Effectively, we are computing:
                // carry = if coef >= 2^(w-1) { 1 } else { 0 }
                // (Here one can view the top bit of coef as a sign bit.)
                carry = (coeff + radix / 2) >> w;
                debug_assert!(carry <= 1);

                // NOTE: if the inputs are always guaranteed to be at most BigInt::MAX,
                // then this is correct even for the last digit.
                let val = coeff as i64 - (carry << w) as i64;
                debug_assert!(val.abs() < (1 << (w - 1)));

                if val >= 0 {
                    val as u64
                } else {
                    (-val - 1) as u64 | sign_mask
                }
            });
        }
    });
}

#[inline(always)]
fn modify_digit(
    scalar: &mut [u64],
    digit_info: &DigitInfo,
    digit_bit_size: u8,
    window_mask: u64,
    f: impl FnOnce(u64) -> u64,
) {
    // Offset into the `u64`'s underlying `scalar`, ...
    let u64_idx = digit_info.u64_idx() as usize;
    let bit_idx = digit_info.bit_idx() as u8;
    let is_single_word = digit_info.is_single_word();

    let digit = read_digit(u64_idx, bit_idx, is_single_word, scalar, window_mask);
    let new_digit = f(digit);

    // Write the new digit back to the scalar.
    // We first clear the bits corresponding to this digit, then write the new value.
    let read_mask = window_mask << bit_idx;
    scalar[u64_idx] &= !read_mask;
    scalar[u64_idx] |= new_digit << bit_idx;

    // Now, if the digit spans two u64's, we need to write the upper bits to the next u64.
    if !is_single_word {
        // First, clear the lower bits of the next word.
        let len = digit_bit_size - (64 - bit_idx);
        let upper_mask = (1u64 << len) - 1;
        scalar[u64_idx + 1] &= !upper_mask;

        // Then, we write the upper bits to the next word.
        let upper = new_digit >> (64 - bit_idx); // bits of `val` that should be written to the next word.
        scalar[u64_idx + 1] |= upper
    }
}

#[inline(always)]
fn read_digit(
    u64_idx: usize,
    bit_idx: u8,
    is_single_word: bool,
    scalar: &[u64],
    window_mask: u64,
) -> u64 {
    if is_single_word {
        (scalar[u64_idx] >> bit_idx) & window_mask
    } else {
        ((scalar[u64_idx] >> bit_idx) | (scalar[u64_idx + 1] << (64 - bit_idx))) & window_mask
    }
}

#[derive(Copy, Clone, Debug)]
struct DigitInfo {
    u64_idx: u8,
    // upper bit = is_single_word,
    // lower 6 bits = bit_idx
    bit_info: u8,
}

impl DigitInfo {
    /// Create a new packed digit descriptor for digit index `i`
    #[inline]
    const fn new(i: usize, w: usize, scalar_len: usize) -> Self {
        let bit_offset = i * w;
        // Offset into the `u64`'s underlying `scalar`, ...
        let u64_idx = (bit_offset / 64) as u8;
        // ... and the bit offset within that `u64`.
        let bit_idx = (bit_offset % 64) as u8;

        // Does this fit in a single u64?
        // This can happen either if
        // 1. this digit's bits do not span two u64's, i.e. bit_idx + w <= 64
        // 2. it's the last u64 anyway.
        let is_single_word = (bit_idx as usize + w < 64) | // (1)
            (u64_idx as usize == scalar_len - 1); // (2)

        // Pack `bit_idx` and `is_single_word` into a single byte.
        // `bit_idx` fits in 6 bits, and `is_single_word` fits in 1 bit.
        // So, we store `bit_idx` in the lower 6 bits, and `is_single_word` in the MSB.
        let bit_info = bit_idx | ((is_single_word as u8) << 7);

        Self { u64_idx, bit_info }
    }

    #[inline]
    const fn bit_idx(&self) -> u8 {
        self.bit_info & 0b0011_1111
    }

    #[inline]
    const fn is_single_word(&self) -> bool {
        (self.bit_info & 0b1000_0000) == 1
    }

    #[inline]
    fn u64_idx(&self) -> u8 {
        self.u64_idx
    }
}
