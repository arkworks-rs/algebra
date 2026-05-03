use super::*;
use crate::small_fp::mul::generate_mul_impl;
use crate::small_fp::utils::{
    compute_large_subgroup_root, compute_two_adic_root_of_unity, compute_two_adicity,
    generate_montgomery_bigint_casts, generate_sqrt_precomputation, mod_mul_const, pow_mod_const,
};
use crate::utils::find_conservative_subgroup_base;

pub(crate) fn backend_impl(
    repr_type: &proc_macro2::TokenStream,
    modulus: u128,
    generator: u128,
) -> (proc_macro2::TokenStream, u128) {
    assert!(modulus > 1, "modulus must be greater than 1");
    assert!(
        modulus % 2 == 1,
        "modulus must be odd for Montgomery multiplication"
    );
    assert!(
        modulus < (1u128 << 64),
        "modulus must be < 2^64 for SmallFp"
    );

    let repr_type_str = repr_type.to_string();

    // R = 2^k_bits where k_bits = ceil(log2(modulus))
    // Since modulus < 2^64, k_bits <= 64 and R always fits in u128
    let k_bits = 128 - modulus.leading_zeros();
    let r: u128 = 1u128 << k_bits;
    let r_mod_n = r % modulus;
    let r_mask = r - 1;

    let n_prime = mod_inverse_pow2(modulus, k_bits);
    let one_mont = r_mod_n;
    let generator_mont = mod_mul_const(generator % modulus, r_mod_n % modulus, modulus);

    let two_adicity = compute_two_adicity(modulus);
    let two_adic_root = compute_two_adic_root_of_unity(modulus, two_adicity, generator);
    let two_adic_root_mont = mod_mul_const(two_adic_root, r_mod_n, modulus);

    let neg_one_mont = mod_mul_const(modulus - 1, r_mod_n, modulus);

    let modulus_big = num_bigint::BigUint::from(modulus);
    let mixed_radix_impl = if let Some((base, power)) =
        find_conservative_subgroup_base(&modulus_big)
    {
        let large_root = compute_large_subgroup_root(modulus, generator, two_adicity, base, power);
        let large_root_mont = mod_mul_const(large_root, r_mod_n, modulus);
        quote! {
            const SMALL_SUBGROUP_BASE: Option<u32> = Some(#base);
            const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = Some(#power);
            const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<SmallFp<Self>> = Some(SmallFp::from_raw(#large_root_mont as Self::T));
        }
    } else {
        quote! {}
    };

    let (from_bigint_impl, into_bigint_impl) = generate_montgomery_bigint_casts();
    let sqrt_precomp_impl = generate_sqrt_precomputation(modulus, two_adicity, Some(r_mod_n));
    let r2 = mod_mul_const(r_mod_n, r_mod_n, modulus);

    // Generate multiplication implementation based on type
    let mul_impl = generate_mul_impl(repr_type, modulus, k_bits, r_mask, n_prime);
    let inverse_impl = generate_inverse_impl(repr_type, modulus, r_mod_n, r2);

    let type_bits = match repr_type_str.as_str() {
        "u8" => 8u32,
        "u16" => 16u32,
        "u32" => 32u32,
        "u64" => 64u32,
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
                    val += Self::T::MAX - Self::MODULUS + 1
                }
                if val >= Self::MODULUS {
                    val -= Self::MODULUS;
                }
                a.value = val;
            }
        }
    };

    let ts = quote! {
        type T = #repr_type;
        const MODULUS: Self::T = #modulus as Self::T;
        const MODULUS_U128: u128 = #modulus;
        const GENERATOR: SmallFp<Self> = SmallFp::from_raw(#generator_mont as Self::T);
        const ZERO: SmallFp<Self> = SmallFp::from_raw(0 as Self::T);
        const ONE: SmallFp<Self> = SmallFp::from_raw(#one_mont as Self::T);
        const NEG_ONE: SmallFp<Self> = SmallFp::from_raw(#neg_one_mont as Self::T);

        const TWO_ADICITY: u32 = #two_adicity;
        const TWO_ADIC_ROOT_OF_UNITY: SmallFp<Self> = SmallFp::from_raw(#two_adic_root_mont as Self::T);

        #mixed_radix_impl

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
    };

    (ts, r_mod_n)
}

// Generate inverse using the binary extended GCD algorithm:
//
// TL;DR: This reduces modular reductions needed to a single modular correction
// It's based on Pornin (2020): https://eprint.iacr.org/2020/1340
//
// But with adaptations for single limb arithmetic made by Plonky3:
// 31-bit fields here: https://github.com/Plonky3/Plonky3/pull/921/changes
// Goldilocks here: https://github.com/Plonky3/Plonky3/pull/925
fn generate_inverse_impl(
    repr_type: &proc_macro2::TokenStream,
    modulus: u128,
    r_mod_n: u128,
    r2: u128,
) -> proc_macro2::TokenStream {
    let repr_type_str = repr_type.to_string();

    let field_bits = 128 - modulus.leading_zeros();
    // num of iterations need to guarantee that rem_1 converges on 1 (meaning GCD is found)
    // Note: only len(a) + len(modulus) iterations are needed but keep this way for constant-time execution
    let num_iters = 2 * field_bits - 2;

    // 2⁻¹ mod P = (P+1)/2  (works because P is odd)
    let half = (modulus + 1) / 2;

    // 2^{-N} mod P = ((P+1)/2)^N mod P
    let two_neg_iters = pow_mod_const(half, num_iters as u128, modulus);

    // R³ = R² · R
    let r3 = mod_mul_const(r2, r_mod_n, modulus);

    // C = R³ · 2^{-N} mod P
    let corr = mod_mul_const(r3, two_neg_iters, modulus);

    #[allow(clippy::if_not_else)]
    if repr_type_str != "u64" {
        // all primes <= u32 branch: bezout coefficients fit in i64, single loop
        quote! {
            #[inline]
            fn inverse(a: &SmallFp<Self>) -> Option<SmallFp<Self>> {
                if a.value == 0 {
                    return None;
                }
                // every round the invariant must hold:
                //   bezout_a · input ≡ rem_a · 2^i  (mod P)
                //   bezout_b · input ≡ rem_b · 2^i  (mod P)
                let mut rem_a: u64 = a.value as u64;
                let mut rem_b: u64 = Self::MODULUS as u64;
                let mut bezout_a: i64 = 1;
                let mut bezout_b: i64 = 0;
                let mut i = 0u32;
                // everything in this loop is add, sub, or bitwise
                while i < #num_iters {
                    // if rem_a is odd
                    if rem_a & 1 != 0 {
                        // if a < b, swap them
                        if rem_a < rem_b {
                            (rem_a, rem_b) = (rem_b, rem_a);
                            (bezout_a, bezout_b) = (bezout_b, bezout_a);
                        }
                        // subtract b from a
                        rem_a -= rem_b;
                        bezout_a -= bezout_b;
                    }
                    // always divide a by 2
                    rem_a >>= 1;
                    // always multiply b by 2
                    bezout_b <<= 1;
                    i += 1;
                }
                // convert signed bezout_b to a field element in [0, P)
                let bezout_canonical = bezout_b.rem_euclid(Self::MODULUS as i64) as u64;
                let mut bezout_b_field = SmallFp::from_raw(bezout_canonical as Self::T);

                // perfom one correction to get a⁻¹·R mod P
                let corr_field = SmallFp::from_raw(#corr as Self::T);
                Self::mul_assign(&mut bezout_b_field, &corr_field);
                Some(bezout_b_field)
            }
        }
    } else {
        // all larger primes: bezout coefficients overflow i64, so we split
        // into two half-rounds and compose the results via matrix multiply.

        // num_iters = 126, which doesn't fit into anything useful, so we must split this into two rounds
        let half_iters = num_iters / 2;
        // we can do 62 iterations in i64 but we need 63 so we promote the last round to i128
        let half_iters_i64 = half_iters - 1;

        quote! {
            #[inline]
            fn inverse(a: &SmallFp<Self>) -> Option<SmallFp<Self>> {
                if a.value == 0 {
                    return None;
                }

                let mut rem_a: u64 = a.value;
                let mut rem_b: u64 = Self::MODULUS;

                // Run two half-rounds, saving the entries needed for composition.
                // Each half-round tracks a 2x2 transition matrix but we only save
                // the entries we actually need for the final composition.

                // ---- half-round 1: save (r1_bezout_a, r1_bezout_b) ----
                let (r1_bezout_a, r1_bezout_b): (i128, i128);
                {
                    let (mut bezout_a, mut mod_a, mut bezout_b, mut mod_b): (i64, i64, i64, i64) = (1, 0, 0, 1);
                    let mut i = 0u32;
                    while i < #half_iters_i64 {
                        if rem_a & 1 != 0 {
                            if rem_a < rem_b {
                                (rem_a, rem_b) = (rem_b, rem_a);
                                (bezout_a, bezout_b) = (bezout_b, bezout_a);
                                (mod_a, mod_b) = (mod_b, mod_a);
                            }
                            rem_a -= rem_b; rem_a >>= 1;
                            bezout_a -= bezout_b; mod_a -= mod_b;
                        } else {
                            rem_a >>= 1;
                        }
                        bezout_b <<= 1; mod_b <<= 1;
                        i += 1;
                    }
                    // final iteration promoted to i128 to avoid ±2^63 overflow
                    let (mut bezout_a, mut mod_a, mut bezout_b, mut mod_b) =
                        (bezout_a as i128, mod_a as i128, bezout_b as i128, mod_b as i128);
                    if rem_a & 1 != 0 {
                        if rem_a < rem_b {
                            (rem_a, rem_b) = (rem_b, rem_a);
                            (bezout_a, bezout_b) = (bezout_b, bezout_a);
                            (mod_a, mod_b) = (mod_b, mod_a);
                        }
                        rem_a -= rem_b; rem_a >>= 1;
                        bezout_a -= bezout_b; mod_a -= mod_b;
                    } else {
                        rem_a >>= 1;
                    }
                    bezout_b <<= 1; mod_b <<= 1;
                    r1_bezout_a = bezout_a; r1_bezout_b = bezout_b;
                }

                // ---- half-round 2: save (r2_bezout_b, r2_mod_b) ----
                let (r2_bezout_b, r2_mod_b): (i128, i128);
                {
                    let (mut bezout_a, mut mod_a, mut bezout_b, mut mod_b): (i64, i64, i64, i64) = (1, 0, 0, 1);
                    let mut i = 0u32;
                    while i < #half_iters_i64 {
                        if rem_a & 1 != 0 {
                            if rem_a < rem_b {
                                (rem_a, rem_b) = (rem_b, rem_a);
                                (bezout_a, bezout_b) = (bezout_b, bezout_a);
                                (mod_a, mod_b) = (mod_b, mod_a);
                            }
                            rem_a -= rem_b; rem_a >>= 1;
                            bezout_a -= bezout_b; mod_a -= mod_b;
                        } else {
                            rem_a >>= 1;
                        }
                        bezout_b <<= 1; mod_b <<= 1;
                        i += 1;
                    }
                    // final iteration promoted to i128 to avoid ±2^63 overflow
                    let (mut bezout_a, mut mod_a, mut bezout_b, mut mod_b) =
                        (bezout_a as i128, mod_a as i128, bezout_b as i128, mod_b as i128);
                    if rem_a & 1 != 0 {
                        if rem_a < rem_b {
                            (rem_a, rem_b) = (rem_b, rem_a);
                            (bezout_a, bezout_b) = (bezout_b, bezout_a);
                            (mod_a, mod_b) = (mod_b, mod_a);
                        }
                        rem_a -= rem_b; rem_a >>= 1;
                        bezout_a -= bezout_b; mod_a -= mod_b;
                    } else {
                        rem_a >>= 1;
                    }
                    bezout_b <<= 1; mod_b <<= 1;
                    r2_bezout_b = bezout_b; r2_mod_b = mod_b;
                }

                // Compose: total bezout_b = r2_bezout_b * r1_bezout_a + r2_mod_b * r1_bezout_b
                let bezout_raw = r2_bezout_b * r1_bezout_a + r2_mod_b * r1_bezout_b;

                // convert signed bezout to a field element in [0, P)
                let p = Self::MODULUS as i128;
                let bezout_canonical = ((bezout_raw % p) + p) as u128 % Self::MODULUS as u128;
                let mut bezout_field = SmallFp::from_raw(bezout_canonical as Self::T);

                // perform one correction to get a⁻¹·R mod P
                let corr_field = SmallFp::from_raw(#corr as Self::T);
                Self::mul_assign(&mut bezout_field, &corr_field);
                Some(bezout_field)
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
    // k_bits <= 64 since modulus < 2^64
    let mask = (1u128 << k_bits) - 1;
    inv.wrapping_neg() & mask
}

pub(crate) fn exit_impl(modulus: u128, r_mod_p: u128) -> proc_macro2::TokenStream {
    quote! {
        pub fn exit(a: &mut SmallFp<Self>) {
            let one = SmallFp::from_raw(1 as <Self as SmallFpConfig>::T);
            <Self as SmallFpConfig>::mul_assign(a, &one);
        }

        // This is the `SmallFp` analogue of [`MontFp!`] to support const initialization
        pub const fn from_u128(value: u128) -> SmallFp<Self> {
            const MODULUS: u128 = #modulus;
            const R_MOD_P: u128 = #r_mod_p;

            // const-compatible modular multiplication via double-and-add
            // Safe from overflow: modulus < 2^64 so a,result < 2^64 and all additions fit u128
            const fn mod_mul(mut a: u128, mut b: u128, m: u128) -> u128 {
                a %= m;
                let mut result = 0u128;
                while b > 0 {
                    if b & 1 == 1 {
                        result = (result + a) % m;
                    }
                    a = (a + a) % m;
                    b >>= 1;
                }
                result
            }

            let val = value % MODULUS;
            let mont = mod_mul(val, R_MOD_P, MODULUS);
            SmallFp::from_raw(mont as <Self as SmallFpConfig>::T)
        }
    }
}
