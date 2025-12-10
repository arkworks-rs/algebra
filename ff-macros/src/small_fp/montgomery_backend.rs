use std::u32;
use super::*;
use crate::small_fp::utils::{
    compute_two_adic_root_of_unity, compute_two_adicity, generate_montgomery_bigint_casts,
    generate_sqrt_precomputation, mod_mul_const,
};

pub(crate) fn backend_impl(
    ty: &proc_macro2::TokenStream,
    modulus: u128,
    generator: u128,
) -> proc_macro2::TokenStream {
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

    let (from_bigint_impl, into_bigint_impl) =
        generate_montgomery_bigint_casts(modulus, k_bits, r_mod_n);
    let sqrt_precomp_impl = generate_sqrt_precomputation(modulus, two_adicity, Some(r_mod_n));

    // Generate multiplication implementation based on type
    let mul_impl = generate_mul_impl(ty, modulus, k_bits, r_mask, n_prime);

    quote! {
        type T = #ty;
        const MODULUS: Self::T = #modulus as Self::T;
        const MODULUS_U128: u128 = #modulus;
        const GENERATOR: SmallFp<Self> = SmallFp::new(#generator_mont as Self::T);
        const ZERO: SmallFp<Self> = SmallFp::new(0 as Self::T);
        const ONE: SmallFp<Self> = SmallFp::new(#one_mont as Self::T);
        const NEG_ONE: SmallFp<Self> = SmallFp::new(#neg_one_mont as Self::T);


        const TWO_ADICITY: u32 = #two_adicity;
        const TWO_ADIC_ROOT_OF_UNITY: SmallFp<Self> = SmallFp::new(#two_adic_root_mont as Self::T);
        #sqrt_precomp_impl

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
            if a.value != (0 as Self::T) {
                a.value = Self::MODULUS - a.value;
            }
        }

        #mul_impl

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
                    let mut acc = SmallFp::new(0 as Self::T);
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

        #from_bigint_impl

        #into_bigint_impl
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
        "u128" => generate_u128_mul(modulus, k_bits, r_mask, n_prime),
        "u64" => generate_u64_mul(modulus, k_bits, r_mask, n_prime),
        "u32" => generate_u32_mul(modulus, k_bits, r_mask, n_prime),
        "u8" | "u16" => generate_small_mul(ty, ty_str.as_str(), modulus, k_bits, r_mask, n_prime),
        _ => panic!("Unsupported type: {}", ty_str),
    }
}

fn generate_u128_mul(
    modulus: u128,
    k_bits: u32,
    r_mask: u128,
    n_prime: u128,
) -> proc_macro2::TokenStream {
    let modulus_lo = modulus & 0xFFFFFFFFFFFFFFFF;
    let modulus_hi = modulus >> 64;
    let shift_back = 128 - k_bits;

    quote! {
        #[inline(always)]
        fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            const MODULUS_LO: u128 = #modulus_lo;
            const MODULUS_HI: u128 = #modulus_hi;
            const R_MASK: u128 = #r_mask;
            const N_PRIME: u128 = #n_prime;

            // 256-bit result stored as lo, hi
            // t = a * b
            let a_lo = a.value & 0xFFFFFFFFFFFFFFFF;
            let a_hi = a.value >> 64;
            let b_lo = b.value & 0xFFFFFFFFFFFFFFFF;
            let b_hi = b.value >> 64;

            let lolo = a_lo * b_lo;
            let lohi = a_lo * b_hi;
            let hilo = a_hi * b_lo;
            let hihi = a_hi * b_hi;

            let (cross_sum, cross_carry) = lohi.overflowing_add(hilo);
            let (t_lo, mid_carry) = lolo.overflowing_add(cross_sum << 64);
            let t_hi = hihi + ((cross_sum >> 64) | ((cross_carry as u128) << 64)) + (mid_carry as u128);

            // m = t_lo * n_prime & r_mask
            let m = t_lo.wrapping_mul(N_PRIME) & R_MASK;

            // mn = m * modulus
            let m_lo = m & 0xFFFFFFFFFFFFFFFF;
            let m_hi = m >> 64;

            let lolo = m_lo * MODULUS_LO;
            let lohi = m_lo * MODULUS_HI;
            let hilo = m_hi * MODULUS_LO;
            let hihi = m_hi * MODULUS_HI;

            let (cross_sum, cross_carry) = lohi.overflowing_add(hilo);
            let (mn_lo, mid_carry) = lolo.overflowing_add(cross_sum << 64);
            let mn_hi = hihi + ((cross_sum >> 64) | ((cross_carry as u128) << 64)) + (mid_carry as u128);

            // (t + mn) / R
            let (sum_lo, carry) = t_lo.overflowing_add(mn_lo);
            let sum_hi = t_hi + mn_hi + (carry as u128);

            let mut u = (sum_lo >> #k_bits) | (sum_hi << #shift_back);
            u -= #modulus * (u >= #modulus) as u128;
            a.value = u;
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

fn mod_inverse_pow2(n: u128, k_bits: u32) -> u128 {
    let mut inv = 1u128;
    for _ in 0..k_bits {
        inv = inv.wrapping_mul(2u128.wrapping_sub(n.wrapping_mul(inv)));
    }
    let mask = (1u128 << k_bits) - 1;
    inv.wrapping_neg() & mask
}

pub(crate) fn new(modulus: u128, _ty: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let k_bits = 128 - modulus.leading_zeros();
    let r: u128 = 1u128 << k_bits;
    let r_mod_n = r % modulus;
    let r2 = mod_mul_const(r_mod_n, r_mod_n, modulus);

    quote! {
        pub fn new(value: <Self as SmallFpConfig>::T) -> SmallFp<Self> {
            let reduced_value = value % <Self as SmallFpConfig>::MODULUS;
            let mut tmp = SmallFp::new(reduced_value);
            let r2_elem = SmallFp::new(#r2 as <Self as SmallFpConfig>::T);
            <Self as SmallFpConfig>::mul_assign(&mut tmp, &r2_elem);
            tmp
        }

        pub fn exit(a: &mut SmallFp<Self>) {
            let mut tmp = *a;
            let one = SmallFp::new(1 as <Self as SmallFpConfig>::T);
            <Self as SmallFpConfig>::mul_assign(&mut tmp, &one);
            a.value = tmp.value;
        }
    }
}
