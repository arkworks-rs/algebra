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
    let two_adic_root = compute_two_adic_root_of_unity(modulus, two_adicity);
    let two_adic_root_mont = mod_mul_const(two_adic_root, r_mod_n, modulus);

    let neg_one_mont = mod_mul_const(modulus - 1, r_mod_n, modulus);

    let (from_bigint_impl, into_bigint_impl) =
        generate_montgomery_bigint_casts(modulus, k_bits, r_mod_n);
    let sqrt_precomp_impl = generate_sqrt_precomputation(modulus, two_adicity);

    // Generate multiplication implementation based on type
    let mul_impl = generate_mul_impl(ty, modulus, k_bits, r_mask, n_prime);

    quote! {
        type T = #ty;
        const MODULUS: Self::T = #modulus as Self::T;
        const MODULUS_128: u128 = #modulus;
        const GENERATOR: SmallFp<Self> = SmallFp::new(#generator_mont as Self::T);
        const ZERO: SmallFp<Self> = SmallFp::new(0 as Self::T);
        const ONE: SmallFp<Self> = SmallFp::new(#one_mont as Self::T);
        const NEG_ONE: SmallFp<Self> = SmallFp::new(#neg_one_mont as Self::T);


        const TWO_ADICITY: u32 = #two_adicity;
        const TWO_ADIC_ROOT_OF_UNITY: SmallFp<Self> = SmallFp::new(#two_adic_root_mont as Self::T);
        #sqrt_precomp_impl

        fn add_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            a.value = match a.value.overflowing_add(b.value) {
                (val, false) => val % Self::MODULUS,
                (val, true) => (Self::T::MAX - Self::MODULUS + 1 + val) % Self::MODULUS,
            };
        }

        fn sub_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            if a.value >= b.value {
                a.value -= b.value;
            } else {
                a.value = Self::MODULUS - (b.value - a.value);
            }
        }

        fn double_in_place(a: &mut SmallFp<Self>) {
            let tmp = *a;
            Self::add_assign(a, &tmp);
        }

        fn neg_in_place(a: &mut SmallFp<Self>) {
            if a.value != (0 as Self::T) {
                a.value = Self::MODULUS - a.value;
            }
        }

        #mul_impl

        fn sum_of_products<const T: usize>(
            a: &[SmallFp<Self>; T],
            b: &[SmallFp<Self>; T],) -> SmallFp<Self> {
            let mut acc = SmallFp::new(0 as Self::T);
            for (x, y) in a.iter().zip(b.iter()) {
                let mut prod = *x;
                Self::mul_assign(&mut prod, y);
                Self::add_assign(&mut acc, &prod);
            }
            acc
        }

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
                Self::mul_assign(&mut sq, &base);
                base = sq;
                exp >>= 1;
            }

            Some(result)
        }

        #from_bigint_impl

        #into_bigint_impl
    }
}

fn generate_mul_impl(
    ty: &proc_macro2::TokenStream,
    modulus: u128,
    k_bits: u32,
    r_mask: u128,
    n_prime: u128,
) -> proc_macro2::TokenStream {
    let ty_str = ty.to_string();

    if ty_str == "u128" {
        quote! {
            #[inline(always)]
            fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                // 256-bit result stored as lo, hi
                // t = a * b
                let lolo = (a.value & 0xFFFFFFFFFFFFFFFF) * (b.value & 0xFFFFFFFFFFFFFFFF);
                let lohi = (a.value & 0xFFFFFFFFFFFFFFFF) * (b.value >> 64);
                let hilo = (a.value >> 64) * (b.value & 0xFFFFFFFFFFFFFFFF);
                let hihi = (a.value >> 64) * (b.value >> 64);

                let (cross_sum, cross_carry) = lohi.overflowing_add(hilo);
                let (mid, mid_carry) = lolo.overflowing_add(cross_sum << 64);
                let t_lo = mid;
                let t_hi = hihi + (cross_sum >> 64) + ((cross_carry as u128) << 64) + (mid_carry as u128);

                // m = t_lo * n_prime & r_mask
                let m = t_lo.wrapping_mul(#n_prime) & #r_mask;

                // mn = m * modulus
                let lolo = (m & 0xFFFFFFFFFFFFFFFF) * (#modulus & 0xFFFFFFFFFFFFFFFF);
                let lohi = (m & 0xFFFFFFFFFFFFFFFF) * (#modulus >> 64);
                let hilo = (m >> 64) * (#modulus & 0xFFFFFFFFFFFFFFFF);
                let hihi = (m >> 64) * (#modulus >> 64);

                let (cross_sum, cross_carry) = lohi.overflowing_add(hilo);
                let (mid, mid_carry) = lolo.overflowing_add(cross_sum << 64);
                let mn_lo = mid;
                let mn_hi = hihi + (cross_sum >> 64) + ((cross_carry as u128) << 64) + (mid_carry as u128);

                // (t + mn) / R
                let (sum_lo, carry) = t_lo.overflowing_add(mn_lo);
                let sum_hi = t_hi + mn_hi + (carry as u128);

                let u = if #k_bits < 128 {
                    (sum_lo >> #k_bits) | (sum_hi << (128 - #k_bits))
                } else {
                    sum_hi >> (#k_bits - 128)
                };

                let u = if u >= #modulus { u - #modulus } else { u };
                a.value = u as Self::T;
            }
        }
    } else {
        let (mul_ty, bits) = match ty_str.as_str() {
            "u8" => (quote! {u16}, 16u32),
            "u16" => (quote! {u32}, 32u32),
            "u32" => (quote! {u64}, 64u32),
            _ => (quote! {u128}, 128u32),
        };

        let r_mask_downcast = quote! { #r_mask as #mul_ty };
        let n_prime_downcast = quote! { #n_prime as #mul_ty };
        let modulus_downcast = quote! { #modulus as #mul_ty };
        let one = quote! { 1 as #mul_ty };

        quote! {
            #[inline(always)]
            fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                let a_val = a.value as #mul_ty;
                let b_val = b.value as #mul_ty;

                let t = a_val * b_val;
                let t_low = t & #r_mask_downcast;

                // m = t_lo * n_prime & r_mask
                let m = t_low.wrapping_mul(#n_prime_downcast) & #r_mask_downcast;

                // mn = m * modulus
                let mn = m * #modulus_downcast;

                // (t + mn) / R
                let (sum, overflow) = t.overflowing_add(mn);
                let mut u = sum >> #k_bits;
                if overflow {
                    u += (#one) << (#bits - #k_bits);
                }

                let u = if u >= #modulus_downcast { u - #modulus_downcast } else { u };
                a.value = u as Self::T;
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
