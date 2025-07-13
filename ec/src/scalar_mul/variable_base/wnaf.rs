use crate::scalar_mul::variable_base::{utils::*, VariableBaseMSM};
use ark_ff::prelude::*;
use ark_std::{vec, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

// Compute msm using windowed non-adjacent form
fn msm_bigint_wnaf_inner<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    bigints: &[<V::ScalarField as PrimeField>::BigInt],
    c: usize,
    digit_infos: &[DigitInfo],
) -> V {
    let size = bases.len().min(bigints.len());
    let scalars = &bigints[..size];
    let bases = &bases[..size];

    let num_bits = V::ScalarField::MODULUS_BIT_SIZE as usize;

    let zero = V::ZERO_BUCKET;
    let num_digits = digit_infos.len();

    let window_mask = (1 << c) - 1;
    let sign_mask = 1 << (c - 1);
    let process_digit = |i: usize, digit_info: &DigitInfo, out: &mut V::Bucket| {
        let mut buckets = if i == num_digits - 1 {
            // No borrow for the last digit
            let final_size = num_bits - (num_digits - 1) * c;
            vec![V::ZERO_BUCKET; 1 << final_size]
        } else {
            vec![V::ZERO_BUCKET; 1 << (c - 1)]
        };
        let u64_idx = digit_info.u64_idx() as usize;
        let bit_idx = digit_info.bit_idx();
        let is_single_word = digit_info.is_single_word();

        for (scalar, base) in scalars.iter().zip(bases) {
            let scalar = scalar.as_ref();
            let coeff = read_digit(u64_idx, bit_idx, is_single_word, scalar, window_mask);

            if i == num_digits - 1 {
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
        *out = zero;
        buckets.into_iter().rev().for_each(|b| {
            running_sum += &b;
            *out += &running_sum;
        });
    };

    let mut window_sums = vec![zero; num_digits];

    // The original code uses rayon. Unfortunately, experiments have shown that
    // rayon does quite sub-optimally for this particular instance, and directly
    // spawning threads was faster.
    #[cfg(feature = "parallel")]
    rayon::scope(|s| {
        use itertools::Itertools;

        let len = window_sums.len();
        for (i, (out, digit_info)) in window_sums.iter_mut().zip_eq(digit_infos).enumerate() {
            if i == len - 1 {
                process_digit(i, digit_info, out);
            } else {
                s.spawn(move |_| {
                    process_digit(i, digit_info, out);
                });
            }
        }
    });

    #[cfg(not(feature = "parallel"))]
    for (i, (out, digit_info)) in window_sums.iter_mut().zip(digit_infos).enumerate() {
        process_digit(i, digit_info, out);
    }

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

/// Computes an MSM using the windowed non-adjacent form (WNAF) algorithm.
/// To improve parallelism, when number of threads is at least 2, this
/// function will split the input into enough chunks so that each chunk
/// can be processed with 2 threads.
pub(super) fn msm_bigint_wnaf<V: VariableBaseMSM>(
    mut bases: &[V::MulBase],
    mut scalars: &mut [<V::ScalarField as PrimeField>::BigInt],
) -> V {
    let size = bases.len().min(scalars.len());
    if size == 0 {
        return V::zero();
    }

    bases = &bases[..size];
    scalars = &mut scalars[..size];
    let c = compute_c(scalars.len());
    let num_bits = V::ScalarField::MODULUS_BIT_SIZE as usize;
    let digit_infos = process_digits(scalars, c, num_bits);

    #[cfg(feature = "parallel")]
    {
        let num_digits = digit_infos.len();
        let cur_num_threads = rayon::current_num_threads();

        // If we have fewer threads than digits, we can just run the whole thing in one go.
        if cur_num_threads <= num_digits {
            return msm_bigint_wnaf_inner::<V>(bases, scalars, c, &digit_infos);
        }

        // Otherwise, we want to split the input into chunks so that each chunk can be processed with `cur_num_threads` chunks.
        let num_chunks = cur_num_threads.div_ceil(num_digits);
        let chunk_size = scalars.len().div_ceil(num_chunks);

        parallelization_helper(scalars, bases, chunk_size, |b, s| {
            msm_bigint_wnaf_inner::<V>(b, s, c, &digit_infos)
        })
    }

    #[cfg(not(feature = "parallel"))]
    msm_bigint_wnaf_inner::<V>(bases, scalars, c, &digit_infos)
}

// Assumes that `a` contains elements in the range [0, BigInt::MAX - 1].
// This allows the last digit to be processed without special handling.
fn process_digits(a: &mut [impl BigInteger], w: usize, num_bits: usize) -> Vec<DigitInfo> {
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
                debug_assert!(val.abs() <= (1 << (w - 1)));

                if val >= 0 {
                    val as u64
                } else {
                    (-val - 1) as u64 | sign_mask
                }
            });
        }
    });
    digit_infos
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
    let u64_idx = digit_info.u64_idx();
    let bit_idx = digit_info.bit_idx();
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

#[derive(Copy, Clone)]
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
        let bit_idx = (((bit_offset % 64) as u8) << 2) >> 2;

        // Does this fit in a single u64?
        // This can happen either if
        // 1. this digit's bits do not span two u64's, i.e. bit_idx + w <= 64
        // 2. it's the last u64 anyway.
        let is_single_word = bit_idx as usize + w <= 64 || // (1)
            (u64_idx as usize == scalar_len - 1); // (2)

        // Pack `bit_idx` and `is_single_word` into a single byte.
        // `bit_idx` fits in 6 bits, and `is_single_word` fits in 1 bit.
        // So, we store `bit_idx` in the lower 6 bits, and `is_single_word` in the MSB.
        let bit_info = bit_idx | ((is_single_word as u8) << 7);

        Self { u64_idx, bit_info }
    }

    #[inline]
    const fn bit_idx(&self) -> u8 {
        (self.bit_info << 1) >> 1
    }

    #[inline]
    const fn is_single_word(&self) -> bool {
        (self.bit_info >> 7) != 0
    }

    #[inline]
    fn u64_idx(&self) -> usize {
        self.u64_idx as usize
    }
}

impl core::fmt::Debug for DigitInfo {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("DigitInfo")
            .field("u64_idx", &self.u64_idx())
            .field("bit_idx", &self.bit_idx())
            .field("is_single_word", &self.is_single_word())
            .finish()
    }
}

fn compute_c(num_scalars: usize) -> usize {
    use ark_std::{cmp::max, log2};
    if num_scalars < 32 {
        3
    } else {
        let log_num_scalars = log2(num_scalars) as usize;
        let start = max(log_num_scalars - log2(log_num_scalars) as usize, 4usize) - 1;
        let end = log_num_scalars;
        let c = (start..end)
            .map(|c| (c, (num_scalars + (1 << c)) / c))
            .min_by_key(|(_, cost)| *cost)
            .unwrap()
            .0 as usize;
        // gnark did not implement c = 17 - 19. 16 is a great point as it's well aligned.
        if (17..20).contains(&c) {
            16
        } else {
            c
        }
    }
}
