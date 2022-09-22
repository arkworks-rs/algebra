use std::str::FromStr;

use num_bigint::BigUint;
use num_traits::One;

mod biginteger;
use biginteger::*;

mod mul;
use mul::*;

mod sum_of_products;
use quote::format_ident;
use sum_of_products::*;

use crate::utils;

pub fn mont_config_helper(
    modulus: BigUint,
    generator: BigUint,
    small_subgroup_base: Option<u32>,
    small_subgroup_power: Option<u32>,
    config_name: proc_macro2::Ident,
) -> proc_macro2::TokenStream {
    // The arithmetic in this library only works if the modulus*2 is smaller than
    // the backing representation. Compute the number of limbs we need.
    let mut limbs = 1usize;
    {
        let mod2 = (&modulus) << 1; // modulus * 2
        let mut cur = BigUint::one() << 64; // always 64-bit limbs for now
        while cur < mod2 {
            limbs += 1;
            cur <<= 64;
        }
    }

    // modulus - 1 = 2^s * t
    let mut trace = &modulus - BigUint::from_str("1").unwrap();
    while !trace.bit(0) {
        trace >>= 1u8;
    }

    // Compute 2^s root of unity given the generator
    let remaining_subgroup_size = match (small_subgroup_base, small_subgroup_power) {
        (Some(base), Some(power)) => Some(&trace / BigUint::from(base).pow(power)),
        (None, None) => None,
        (..) => panic!("Must specify both `small_subgroup_base` and `small_subgroup_power`"),
    };
    let two_adic_root_of_unity = generator.modpow(&trace, &modulus);
    let large_subgroup_generator = remaining_subgroup_size
        .as_ref()
        .map(|e| generator.modpow(e, &modulus).to_string());
    let modulus = modulus.to_string();
    let generator = generator.to_string();
    let two_adic_root_of_unity = two_adic_root_of_unity.to_string();
    let modulus_limbs = utils::str_to_limbs_u64(&modulus).1;
    let can_use_no_carry_mul_opt = {
        let first_limb_check = *modulus_limbs.last().unwrap() < (u64::MAX >> 1);
        if limbs != 1 {
            first_limb_check && modulus_limbs[..limbs - 1].iter().any(|l| *l != u64::MAX)
        } else {
            first_limb_check
        }
    };
    let modulus = quote::quote! { BigInt([ #( #modulus_limbs ),* ]) };

    let add_with_carry = add_with_carry_impl(limbs);
    let sub_with_borrow = sub_with_borrow_impl(limbs);
    let subtract_modulus = subtract_modulus_impl(&modulus);
    let mul_assign = mul_assign_impl(can_use_no_carry_mul_opt, limbs, &modulus_limbs);
    let sum_of_products = sum_of_products_impl(limbs, &modulus_limbs);

    let mixed_radix = if let Some(large_subgroup_generator) = large_subgroup_generator {
        quote::quote! {
            const SMALL_SUBGROUP_BASE: Option<u32> = Some(#small_subgroup_base);

            const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = Some(#small_subgroup_power);

            const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<F> = Some(ark_ff::MontFp!(#large_subgroup_generator));
        }
    } else {
        quote::quote! {}
    };
    let mod_name = format_ident!("{}___", config_name.to_string().to_lowercase());
    quote::quote! {
        fn #mod_name() {
            use ark_ff::{Field, PrimeField, fields::Fp, BigInt, BigInteger, biginteger::arithmetic as fa, fields::*};
            type B = BigInt<#limbs>;
            type F = Fp<MontBackend<#config_name, #limbs>, #limbs>;

            #[automatically_derived]
            impl MontConfig<#limbs> for #config_name {
                const MODULUS: B = #modulus;

                const GENERATOR: F = ark_ff::MontFp!(#generator);

                const TWO_ADIC_ROOT_OF_UNITY: F = ark_ff::MontFp!(#two_adic_root_of_unity);

                #mixed_radix

                #[inline(always)]
                fn add_assign(a: &mut F, b: &F) {
                    __add_with_carry(&mut a.0, &b.0);
                    __subtract_modulus(a);
                }

                #[inline(always)]
                fn sub_assign(a: &mut F, b: &F) {
                    // If `other` is larger than `self`, add the modulus to self first.
                    if b.0 > a.0 {
                        __add_with_carry(&mut a.0, &#modulus);
                    }
                    __sub_with_borrow(&mut a.0, &b.0);
                }

                #[inline(always)]
                fn double_in_place(a: &mut F) {
                    // This cannot exceed the backing capacity.
                    a.0.mul2();
                    // However, it may need to be reduced.
                    __subtract_modulus(a);
                }

                /// Sets `a = -a`.
                #[inline(always)]
                fn neg_in_place(a: &mut F) {
                    if *a != F::ZERO {
                        let mut tmp = #modulus;
                        __sub_with_borrow(&mut tmp, &a.0);
                        a.0 = tmp;
                    }
                }

                #[inline(always)]
                fn mul_assign(a: &mut F, b: &F) {
                    #mul_assign
                }

                fn sum_of_products<const M: usize>(
                    a: &[F; M],
                    b: &[F; M],
                ) -> F {
                    #sum_of_products
                }
            }

            #subtract_modulus

            #add_with_carry

            #sub_with_borrow
        }
    }
    .into()
}
