use super::*;
use crate::small_fp::utils::{
    compute_two_adic_root_of_unity, compute_two_adicity, generate_montgomery_bigint_casts,
    generate_sqrt_precomputation, mod_mul_const, pow_mod_const,
};

pub(crate) fn backend_impl(
    ty: &proc_macro2::TokenStream,
    modulus: u128,
    generator: u128,
) -> proc_macro2::TokenStream {
    assert!(modulus > 1, "modulus must be greater than 1");
    assert!(
        modulus % 2 == 1,
        "modulus must be odd for Montgomery multiplication"
    );
    assert!(
        modulus < (1u128 << 127),
        "modulus must be < 2^127 for u128-backed SmallFp"
    );

    let ty_str = ty.to_string();
    let is_u128 = ty_str == "u128";

    // For u128, we use R = 2^128 for smaller types, R = 2^k_bits
    let k_bits = if is_u128 {
        128u32
    } else {
        128 - modulus.leading_zeros()
    };
    let r: u128 = if k_bits == 128 {
        0u128
    } else {
        1u128 << k_bits
    };
    // When R = 2^128 this doesn't fit in u128 but:
    // (2^128 - n) mod n  =  2^128 mod n
    // and in u128 wrapping arithmetic:
    // 0 - n wraps to 2^128 - n
    // so:
    // 2^128 mod n = (0 - n) mod n
    let r_mod_n = if k_bits == 128 {
        0u128.wrapping_sub(modulus) % modulus
    } else {
        r % modulus
    };
    let r_mask = if k_bits == 128 { u128::MAX } else { r - 1 };

    let n_prime = mod_inverse_pow2(modulus, k_bits);
    let one_mont = r_mod_n;
    let generator_mont = mod_mul_const(generator % modulus, r_mod_n % modulus, modulus);

    let two_adicity = compute_two_adicity(modulus);
    let two_adic_root = compute_two_adic_root_of_unity(modulus, two_adicity, generator);
    let two_adic_root_mont = mod_mul_const(two_adic_root, r_mod_n, modulus);

    let neg_one_mont = mod_mul_const(modulus - 1, r_mod_n, modulus);

    let (from_bigint_impl, into_bigint_impl) = generate_montgomery_bigint_casts();
    let sqrt_precomp_impl = generate_sqrt_precomputation(modulus, two_adicity, Some(r_mod_n));
    let r2 = mod_mul_const(r_mod_n, r_mod_n, modulus);

    // Generate multiplication implementation based on type
    let mul_impl = generate_mul_impl(ty, modulus, k_bits, r_mask, n_prime);
    let inverse_impl = generate_inverse_impl(ty, modulus, r_mod_n, r2);

    let type_bits = match ty_str.as_str() {
        "u8" => 8u32,
        "u16" => 16u32,
        "u32" => 32u32,
        "u64" => 64u32,
        "u128" => 128u32,
        _ => panic!("unsupported type"),
    };

    // If there is a spare bit skip the overflow branch
    let has_spare_bit = modulus.leading_zeros() >= (128 - type_bits + 1);
    let add_assign_impl = if has_spare_bit {
        quote! {
            #[inline(always)]
            fn add_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                let val = a.value.wrapping_add(b.value);
                a.value = if val >= Self::MODULUS { val - Self::MODULUS } else { val };
            }
        }
    } else {
        quote! {
            #[inline(always)]
            fn add_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                let (mut val, overflow) = a.value.overflowing_add(b.value);
                if overflow {
                    val = Self::T::MAX - Self::MODULUS + 1 + val
                }
                if val >= Self::MODULUS {
                    val -= Self::MODULUS;
                }
                a.value = val;
            }
        }
    };

    quote! {
        type T = #ty;
        const MODULUS: Self::T = #modulus as Self::T;
        const MODULUS_U128: u128 = #modulus;
        const GENERATOR: SmallFp<Self> = SmallFp::from_raw(#generator_mont as Self::T);
        const ZERO: SmallFp<Self> = SmallFp::from_raw(0 as Self::T);
        const ONE: SmallFp<Self> = SmallFp::from_raw(#one_mont as Self::T);
        const NEG_ONE: SmallFp<Self> = SmallFp::from_raw(#neg_one_mont as Self::T);

        const TWO_ADICITY: u32 = #two_adicity;
        const TWO_ADIC_ROOT_OF_UNITY: SmallFp<Self> = SmallFp::from_raw(#two_adic_root_mont as Self::T);

        #sqrt_precomp_impl

        #add_assign_impl

        #[inline(always)]
        fn sub_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            if a.value >= b.value {
                a.value -= b.value;
            } else {
                a.value = Self::MODULUS - (b.value - a.value);
            }
        }

        #[inline(always)]
        fn double_in_place(a: &mut SmallFp<Self>) {
            let tmp = *a;
            Self::add_assign(a, &tmp);
        }

        #[inline(always)]
        fn neg_in_place(a: &mut SmallFp<Self>) {
            if a.value != Self::ZERO.value {
                a.value = Self::MODULUS - a.value;
            }
        }

        #mul_impl

        #inverse_impl

        #[inline(always)]
        fn sum_of_products<const T: usize>(
            a: &[SmallFp<Self>; T],
            b: &[SmallFp<Self>; T],) -> SmallFp<Self> {
            match T {
                1 => {
                    let mut prod = a[0];
                    Self::mul_assign(&mut prod, &b[0]);
                    prod
                },
                2 => {
                    let mut prod1 = a[0];
                    Self::mul_assign(&mut prod1, &b[0]);
                    let mut prod2 = a[1];
                    Self::mul_assign(&mut prod2, &b[1]);
                    Self::add_assign(&mut prod1, &prod2);
                    prod1
                },
                _ => {
                    let mut acc = Self::ZERO;
                    for (x, y) in a.iter().zip(b.iter()) {
                        let mut prod = *x;
                        Self::mul_assign(&mut prod, y);
                        Self::add_assign(&mut acc, &prod);
                    }
                    acc
                }
            }
        }

        #[inline(always)]
        fn square_in_place(a: &mut SmallFp<Self>) {
            let tmp = *a;
            Self::mul_assign(a, &tmp);
        }

        #[inline]
        fn new(value: Self::T) -> SmallFp<Self> {
            let reduced_value = value % Self::MODULUS;
            let mut tmp = SmallFp::from_raw(reduced_value);
            let r2_elem = SmallFp::from_raw(#r2 as Self::T);
            Self::mul_assign(&mut tmp, &r2_elem);
            tmp
        }

        #from_bigint_impl

        #into_bigint_impl
    }
}

// Generates the inverse function using the binary extended GCD algorithm for u8/u16/u32/u64
// fields, falling back to Fermat's little theorem for u128 fields.
//
// The GCD algorithm runs for NUM_ITERS = 2*FIELD_BITS - 2 iterations of cheap integer ops
// (no modular reduction), returning v ≡ 2^NUM_ITERS · (a·R)^{-1} (mod P). A single
// Montgomery multiplication by the precomputed constant C = R^3 · 2^{-NUM_ITERS} mod P
// then corrects the result to a^{-1}·R mod P (the Montgomery form of the inverse).
fn generate_inverse_impl(
    ty: &proc_macro2::TokenStream,
    modulus: u128,
    r_mod_n: u128,
    r2: u128,
) -> proc_macro2::TokenStream {
    let ty_str = ty.to_string();

    if ty_str == "u128" {
        // GCD coefficients would require 256-bit signed integers; use Fermat's little theorem.
        return quote! {
            fn inverse(a: &SmallFp<Self>) -> Option<SmallFp<Self>> {
                if a.value == 0 {
                    return None;
                }
                let mut result = Self::ONE;
                let mut base = *a;
                let mut exp = Self::MODULUS - 2;
                while exp > 0 {
                    if exp & 1 == 1 {
                        Self::mul_assign(&mut result, &base);
                    }
                    let mut sq = base;
                    Self::square_in_place(&mut sq);
                    base = sq;
                    exp >>= 1;
                }
                Some(result)
            }
        };
    }

    // FIELD_BITS = bit-length of modulus; NUM_ITERS = 2*FIELD_BITS - 2 ensures convergence.
    let field_bits = 128 - modulus.leading_zeros();
    let num_iters = 2 * field_bits - 2;

    // Correction constant: C = R^3 · 2^{-NUM_ITERS} mod P
    //   2^{-1} mod P = (P+1)/2  (P is odd)
    //   2^{-NUM_ITERS} mod P = ((P+1)/2)^NUM_ITERS mod P
    let half = (modulus + 1) / 2;
    let two_neg_iters = pow_mod_const(half, num_iters as u128, modulus);
    let r3 = mod_mul_const(r2, r_mod_n, modulus);
    let corr = mod_mul_const(r3, two_neg_iters, modulus);

    if ty_str == "u64" {
        // Two-round binary extended GCD for 64-bit fields (Plonky3 approach).
        //
        // Split NUM_ITERS into two rounds of half_iters each. (a, b) stay u64 since
        // they're always in [0, P). The first (half_iters − 1) iterations per round
        // use i64 matrix entries (|entry| ≤ 2^{HALF_ITERS−1} ≤ 2^62, no overflow).
        // The final iteration of each round is promoted to i128 to safely handle the
        // subtraction/shift that would otherwise produce ±2^63, which is out of i64
        // range. Recombination: sum = f11*f00 + g11*f10 in i128 (≤ 2^126 < 2^127).
        // Note: the final modular reduction uses u128 to handle P ≈ 2^64 where
        // (sum % p) + p can reach ~2P ≈ 2^65, overflowing u64.

        let half_iters = num_iters / 2;
        let half_iters_i64 = half_iters - 1; // iterations using i64, one fewer per round

        quote! {
            #[inline]
            fn inverse(a: &SmallFp<Self>) -> Option<SmallFp<Self>> {
                if a.value == 0 {
                    return None;
                }
                // Invariant per round after k iters: f0·a0 ≡ aa·2^k  (mod P)
                //                                   f1·a0 ≡ bb·2^k  (mod P)
                let mut aa: u64 = a.value;
                let mut bb: u64 = Self::MODULUS;

                // ---- Round 1: produces (f00, f10) in i128 ----
                let (f00, f10): (i128, i128);
                {
                    let (mut f0, mut g0, mut f1, mut g1): (i64, i64, i64, i64) = (1, 0, 0, 1);
                    // First (half_iters − 1) iterations in i64: |entry| ≤ 2^{half_iters−1} ≤ 2^62
                    let mut i = 0u32;
                    while i < #half_iters_i64 {
                        if aa & 1 != 0 {
                            if aa < bb {
                                let t = aa; aa = bb; bb = t;
                                let t = f0; f0 = f1; f1 = t;
                                let t = g0; g0 = g1; g1 = t;
                            }
                            aa -= bb; aa >>= 1;
                            f0 -= f1; g0 -= g1;
                        } else {
                            aa >>= 1;
                        }
                        f1 <<= 1; g1 <<= 1;
                        i += 1;
                    }
                    // Final iteration in i128 to avoid ±2^63 overflow
                    let (mut f0, mut g0, mut f1, mut g1) =
                        (f0 as i128, g0 as i128, f1 as i128, g1 as i128);
                    if aa & 1 != 0 {
                        if aa < bb {
                            let t = aa; aa = bb; bb = t;
                            let t = f0; f0 = f1; f1 = t;
                            let t = g0; g0 = g1; g1 = t;
                        }
                        aa -= bb; aa >>= 1; f0 -= f1; g0 -= g1;
                    } else {
                        aa >>= 1;
                    }
                    f1 <<= 1; g1 <<= 1;
                    f00 = f0; f10 = f1;
                }

                // ---- Round 2: identical structure, produces (f11, g11) ----
                let (f11, g11): (i128, i128);
                {
                    let (mut f0, mut g0, mut f1, mut g1): (i64, i64, i64, i64) = (1, 0, 0, 1);
                    let mut i = 0u32;
                    while i < #half_iters_i64 {
                        if aa & 1 != 0 {
                            if aa < bb {
                                let t = aa; aa = bb; bb = t;
                                let t = f0; f0 = f1; f1 = t;
                                let t = g0; g0 = g1; g1 = t;
                            }
                            aa -= bb; aa >>= 1;
                            f0 -= f1; g0 -= g1;
                        } else {
                            aa >>= 1;
                        }
                        f1 <<= 1; g1 <<= 1;
                        i += 1;
                    }
                    let (mut f0, mut g0, mut f1, mut g1) =
                        (f0 as i128, g0 as i128, f1 as i128, g1 as i128);
                    if aa & 1 != 0 {
                        if aa < bb {
                            let t = aa; aa = bb; bb = t;
                            let t = f0; f0 = f1; f1 = t;
                            let t = g0; g0 = g1; g1 = t;
                        }
                        aa -= bb; aa >>= 1; f0 -= f1; g0 -= g1;
                    } else {
                        aa >>= 1;
                    }
                    f1 <<= 1; g1 <<= 1;
                    f11 = f1; g11 = g1;
                }

                // sum = f11*f00 + g11*f10 ≡ (a·R)^{-1} · 2^{NUM_ITERS} (mod P)
                // Each factor ≤ 2^63 in magnitude ⇒ product ≤ 2^126 < i128::MAX.
                let sum_raw = f11 * f00 + g11 * f10;
                let p = Self::MODULUS as i128;
                // Use u128 for intermediate: (sum % p) + p can reach ~2P ≈ 2^65 for
                // 64-bit moduli, which overflows u64.
                let sum_reduced = ((sum_raw % p) + p) as u128 % Self::MODULUS as u128;
                // Multiply by C = R^3 · 2^{-NUM_ITERS} mod P to get a^{-1}·R mod P
                let mut result = SmallFp::from_raw(sum_reduced as Self::T);
                let corr = SmallFp::from_raw(#corr as Self::T);
                Self::mul_assign(&mut result, &corr);
                Some(result)
            }
        }
    } else {
        // u8, u16, u32: GCD coefficients fit in i64 (|v| ≤ 2^{2*32-2} = 2^62 < 2^63)
        quote! {
            #[inline]
            fn inverse(a: &SmallFp<Self>) -> Option<SmallFp<Self>> {
                if a.value == 0 {
                    return None;
                }
                // Binary extended GCD: v = 2^NUM_ITERS · (a·R)^{-1} mod P
                let mut aa: u64 = a.value as u64;
                let mut bb: u64 = Self::MODULUS as u64;
                let mut u: i64 = 1;
                let mut v: i64 = 0;
                let mut i = 0u32;
                while i < #num_iters {
                    if aa & 1 != 0 {
                        if aa < bb {
                            let tmp_a = aa; aa = bb; bb = tmp_a;
                            let tmp_u = u;  u = v;  v = tmp_u;
                        }
                        aa -= bb;
                        u -= v;
                    }
                    aa >>= 1;
                    v <<= 1;
                    i += 1;
                }
                let p = Self::MODULUS as i64;
                let v_reduced = ((v % p) + p) as u64 % Self::MODULUS as u64;
                // Multiply by C = R^3 · 2^{-NUM_ITERS} mod P to get a^{-1}·R mod P
                let mut result = SmallFp::from_raw(v_reduced as Self::T);
                let corr = SmallFp::from_raw(#corr as Self::T);
                Self::mul_assign(&mut result, &corr);
                Some(result)
            }
        }
    }
}

// Selects the appropriate multiplication algorithm at compile time:
// if modulus <= u64, multiply by casting to the next largest primitive
// otherwise, multiply in parts to form a 256-bit product
fn generate_mul_impl(
    ty: &proc_macro2::TokenStream,
    modulus: u128,
    k_bits: u32,
    r_mask: u128,
    n_prime: u128,
) -> proc_macro2::TokenStream {
    let ty_str = ty.to_string();

    match ty_str.as_str() {
        "u128" => generate_u128_mul(modulus, n_prime),
        "u64" => generate_u64_mul(modulus, k_bits, r_mask, n_prime),
        "u32" => generate_u32_mul(modulus, k_bits, r_mask, n_prime),
        "u8" | "u16" => generate_small_mul(ty, ty_str.as_str(), modulus, k_bits, r_mask, n_prime),
        _ => panic!("Unsupported type: {}", ty_str),
    }
}

// Montgomery multiplication for 2 limbs (similar to ff-asm/src/lib.rs)
fn generate_u128_mul(modulus: u128, n_prime: u128) -> proc_macro2::TokenStream {
    let modulus_lo = (modulus & 0xFFFFFFFFFFFFFFFF) as u64;
    let modulus_hi = (modulus >> 64) as u64;

    quote! {
        #[inline(always)]
        fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            const MODULUS: [u64; 2] = [#modulus_lo, #modulus_hi];
            const INV: u64 = #n_prime as u64;

            let a_limbs = [a.value as u64, (a.value >> 64) as u64];
            let b_limbs = [b.value as u64, (b.value >> 64) as u64];

            #[inline(always)]
            fn umul(a: u64, b: u64) -> (u64, u64) {
                let full = (a as u128) * (b as u128);
                (full as u64, (full >> 64) as u64)
            }

            // r accumulator: 3 words (r[0], r[1], r[2]) to hold intermediate
            let mut r0: u64 = 0;
            let mut r1: u64 = 0;
            let mut r2: u64 = 0;


            let (lo, hi) = umul(a_limbs[0], b_limbs[0]);
            let (r0_new, c) = r0.overflowing_add(lo);
            r0 = r0_new;
            let carry1 = c as u64;

            let (lo, hi2) = umul(a_limbs[1], b_limbs[0]);
            let (r1_new, c1) = r1.overflowing_add(lo);
            let (r1_new, c2) = r1_new.overflowing_add(hi + carry1);
            r1 = r1_new;
            r2 = r2.wrapping_add(hi2).wrapping_add(c1 as u64 + c2 as u64);

            let m = r0.wrapping_mul(INV);

            let (lo, hi) = umul(m, MODULUS[0]);
            let (_, c) = r0.overflowing_add(lo);   // r0 + lo should be 0 mod 2^64
            let carry = hi.wrapping_add(c as u64);

            let (lo, hi) = umul(m, MODULUS[1]);
            let (new_r0, c1) = r1.overflowing_add(lo);
            let (new_r0, c2) = new_r0.overflowing_add(carry);
            r0 = new_r0;
            r1 = r2.wrapping_add(hi).wrapping_add(c1 as u64 + c2 as u64);
            r2 = 0;


            let (lo, hi) = umul(a_limbs[0], b_limbs[1]);
            let (r0_new, c) = r0.overflowing_add(lo);
            r0 = r0_new;
            let carry1 = c as u64;

            let (lo, hi2) = umul(a_limbs[1], b_limbs[1]);
            let (r1_new, c1) = r1.overflowing_add(lo);
            let (r1_new, c2) = r1_new.overflowing_add(hi + carry1);
            r1 = r1_new;
            r2 = r2.wrapping_add(hi2).wrapping_add(c1 as u64 + c2 as u64);

            let m = r0.wrapping_mul(INV);

            let (lo, hi) = umul(m, MODULUS[0]);
            let (_, c) = r0.overflowing_add(lo);
            let carry = hi.wrapping_add(c as u64);

            let (lo, hi) = umul(m, MODULUS[1]);
            let (new_r0, c1) = r1.overflowing_add(lo);
            let (new_r0, c2) = new_r0.overflowing_add(carry);
            r0 = new_r0;
            r1 = r2.wrapping_add(hi).wrapping_add(c1 as u64 + c2 as u64);


            let mut result = (r0 as u128) | ((r1 as u128) << 64);
            let modulus_val = (#modulus_lo as u128) | ((#modulus_hi as u128) << 64);
            if result >= modulus_val {
                result -= modulus_val;
            }
            a.value = result;
        }
    }
}

fn generate_u64_mul(
    modulus: u128,
    k_bits: u32,
    r_mask: u128,
    n_prime: u128,
) -> proc_macro2::TokenStream {
    // Use u128 for multiplication to avoid overflow when multiplying u64 values
    let shift_bits = 128 - k_bits;

    quote! {
        #[inline(always)]
        fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            const MODULUS_MUL_TY: u128 = #modulus as u128;
            const N_PRIME: u128 = #n_prime as u128;
            const R_MASK: u128 = #r_mask as u128;

            let mut t = (a.value as u128) * (b.value as u128);
            let k = t.wrapping_mul(N_PRIME) & R_MASK;
            let (t, overflow) = t.overflowing_add(k * MODULUS_MUL_TY);

            let mut r = (t >> #k_bits) + ((overflow as u128) << #shift_bits);
            if r >= MODULUS_MUL_TY {
                r -= MODULUS_MUL_TY;
            }
            a.value = r as u64;
        }
    }
}

fn generate_u32_mul(
    modulus: u128,
    k_bits: u32,
    r_mask: u128,
    n_prime: u128,
) -> proc_macro2::TokenStream {
    const M31_PRIME: u128 = 2147483647; // 2^31 - 1

    if modulus == M31_PRIME {
        quote! {
           #[inline(always)]
            fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                const K: u64 = 31;
                const MODULUS: u64 = (1u64 << K) - 1;

                let prod = (a.value as u64) * (b.value as u64);
                let mut r = (prod & MODULUS) + (prod >> K);

                if r >= MODULUS {
                    r -= MODULUS;
                }
                a.value = r as u32;
            }
        }
    } else {
        quote! {
            #[inline(always)]
            fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                const MODULUS_MUL_TY: u64 = #modulus as u64;
                const N_PRIME: u64 = #n_prime as u64;
                const R_MASK: u64 = #r_mask as u64;

                let t = (a.value as u64) * (b.value as u64);
                let k = t.wrapping_mul(N_PRIME) & R_MASK;

                let mut r = (t + (k * MODULUS_MUL_TY)) >> #k_bits;
                if r >= MODULUS_MUL_TY {
                   r -= MODULUS_MUL_TY;
                }
                a.value = r as u32;
            }
        }
    }
}

fn generate_small_mul(
    ty: &proc_macro2::TokenStream,
    ty_str: &str,
    modulus: u128,
    k_bits: u32,
    r_mask: u128,
    n_prime: u128,
) -> proc_macro2::TokenStream {
    const M7_PRIME: u128 = 127; // 2^7 - 1
    const M13_PRIME: u128 = 8191; // 2^13 - 1

    if modulus == M7_PRIME {
        quote! {
            #[inline(always)]
            fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                const K: u16 = 7;
                const MODULUS: u16 = (1u16 << K) - 1;

                let prod = (a.value as u16) * (b.value as u16);
                let mut r = (prod & MODULUS) + (prod >> K);

                if r >= MODULUS {
                    r -= MODULUS;
                }
                a.value = r as u8;
            }
        }
    } else if modulus == M13_PRIME {
        quote! {
            #[inline(always)]
            fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                const K: u32 = 13;
                const MODULUS: u32 = (1u32 << K) - 1;

                let prod = (a.value as u32) * (b.value as u32);
                let mut r = (prod & MODULUS) + (prod >> K);

                if r >= MODULUS {
                    r -= MODULUS;
                }
                a.value = r as u16;
            }
        }
    } else {
        let mul_ty = match ty_str {
            "u8" => quote! { u16 },
            "u16" => quote! { u32 },
            _ => unreachable!(),
        };

        quote! {
            #[inline(always)]
            fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                const MODULUS_MUL_TY: #mul_ty = #modulus as #mul_ty;
                const MODULUS_TY: #ty = #modulus as #ty;
                const N_PRIME: #ty = #n_prime as #ty;
                const MASK: #mul_ty = #r_mask as #mul_ty;
                const K_BITS: u32 = #k_bits;

                let a_val = a.value as #mul_ty;
                let b_val = b.value as #mul_ty;

                let tmp = a_val * b_val;
                let carry1 = (tmp >> K_BITS) as #ty;
                let r = (tmp & MASK) as #ty;
                let m = r.wrapping_mul(N_PRIME);

                let tmp = (r as #mul_ty) + ((m as #mul_ty) * MODULUS_MUL_TY);
                let carry2 = (tmp >> K_BITS) as #ty;

                let mut r = (carry1 as #mul_ty) + (carry2 as #mul_ty);
                if r >= MODULUS_MUL_TY {
                    r -= MODULUS_MUL_TY;
                }
                a.value = r as #ty;
            }
        }
    }
}

// Computes -n^-1 mod R by the Newton-Raphson iteration
// This is a special case for inverse modulo power of 2
fn mod_inverse_pow2(n: u128, k_bits: u32) -> u128 {
    const ITER: usize = 7; // log2(128)
    let mut inv = 1u128;

    for _ in 0..ITER {
        inv = inv.wrapping_mul(2u128.wrapping_sub(n.wrapping_mul(inv)));
    }
    let mask = if k_bits == 128 {
        u128::MAX
    } else {
        (1u128 << k_bits) - 1
    };
    inv.wrapping_neg() & mask
}

pub(crate) fn exit_impl() -> proc_macro2::TokenStream {
    quote! {
        pub fn exit(a: &mut SmallFp<Self>) {
            let one = SmallFp::from_raw(1 as <Self as SmallFpConfig>::T);
            <Self as SmallFpConfig>::mul_assign(a, &one);
        }
    }
}
