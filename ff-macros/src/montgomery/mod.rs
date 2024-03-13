use std::str::FromStr;

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::One;

mod biginteger;
use biginteger::{add_with_carry_impl, sub_with_borrow_impl, subtract_modulus_impl};

mod add;
use add::add_assign_impl;
mod double;
use double::double_in_place_impl;
mod mul;
use mul::mul_assign_impl;

mod square;
use square::square_in_place_impl;

mod sum_of_products;
use sum_of_products::sum_of_products_impl;

use crate::utils;

struct LimbMetadata {
    size: usize,
    biguint_macro: proc_macro2::TokenStream,
    bigint_type: proc_macro2::TokenStream,
}

// new LimbMetadata based on the enum
impl LimbMetadata {
    fn new(variant: LimbVariant) -> Self {
        match variant {
            LimbVariant::U32 => Self {
                size: 32,
                biguint_macro: quote::quote!(ark_ff::BigInt32!),
                bigint_type: quote::quote!(BigInt32),
            },
            LimbVariant::U64 => Self {
                size: 64,
                biguint_macro: quote::quote!(ark_ff::BigInt64!),
                bigint_type: quote::quote!(BigInt64),
            },
        }
    }
}

enum LimbVariant {
    U32,
    U64,
}

pub fn mont_config_helper(
    // The modulus p of the field
    modulus: BigUint,
    generator: BigUint,
    small_subgroup_base: Option<u32>,
    small_subgroup_power: Option<u32>,
    config_name: proc_macro2::Ident,
) -> proc_macro2::TokenStream {
    // we can figure out the limb size by inspecting the modulus
    let limb_meta: LimbMetadata = if modulus.next_multiple_of(&BigUint::from(1u64 << 32))
        == modulus.next_multiple_of(&BigUint::from(1u128 << 64))
    {
        LimbMetadata::new(LimbVariant::U64)
    } else {
        // TODO uncomment this once we have u32 limbs support
        // LimbMetadata::new(LimbVariant::U32)
        LimbMetadata::new(LimbVariant::U64)
    };

    let mut limbs = 1usize;
    {
        let mut cur = BigUint::one() << limb_meta.size; // always 64-bit limbs for now
        while cur < modulus {
            limbs += 1;
            cur <<= limb_meta.size;
        }
    }

    // Compute trace t and 2-adicity s such that p - 1 = 2^s * t
    let mut trace = &modulus - BigUint::from_str("1").unwrap();
    while !trace.bit(0) {
        trace >>= 1u8;
    }

    let two_adicity = (&modulus - 1u8)
        .trailing_zeros()
        .expect("two_adicity should fit in u32") as u32;

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

    // Compute R = 2**(64 * limbs) mod m
    let r = (BigUint::one() << (limbs * limb_meta.size)) % &modulus;
    let r_squared = ((&r * &r) % &modulus).to_string();
    let r = r.to_string();
    let modulus_mod_4 = (&modulus % 4u64).try_into().unwrap();

    let modulus_plus_one_div_four = ((&modulus + 1u8) / 4u8).to_u64_digits();
    let trace_minus_one_div_two = ((&trace - 1u8) / 2u8).to_u64_digits();
    let sqrt_precomp = match modulus_mod_4 {
        3 => quote::quote!(Some(SqrtPrecomputation::Case3Mod4 {
            modulus_plus_one_div_four: &[ #( #modulus_plus_one_div_four ),* ]
        })),
        1 => quote::quote!(Some(SqrtPrecomputation::TonelliShanks  {
            two_adicity: Self::TWO_ADICITY,
            quadratic_nonresidue_to_trace: Self::TWO_ADIC_ROOT_OF_UNITY,
            trace_of_modulus_minus_one_div_two: &[ #( #trace_minus_one_div_two ),* ]
        })),
        _ => panic!("Modulus must be odd"),
    };

    let bigint_import = limb_meta.bigint_type.clone();

    let modulus_plus_one_div_four = if modulus_mod_4 == 3u8 {
        quote::quote! { Some(#bigint_import([ #( #modulus_plus_one_div_four  ),* ])) }
    } else {
        quote::quote! { None }
    };

    let modulus = modulus.to_string();
    let generator = generator.to_string();
    let two_adic_root_of_unity = two_adic_root_of_unity.to_string();

    let modulus_limbs = utils::str_to_limbs_u64(&modulus).1;
    let modulus_has_spare_bit = modulus_limbs.last().unwrap() >> 63 == 0;
    let can_use_no_carry_mul_opt = {
        let first_limb_check = *modulus_limbs.last().unwrap() < (u64::MAX >> 1);
        if limbs != 1 {
            first_limb_check && modulus_limbs[..limbs - 1].iter().any(|l| *l != u64::MAX)
        } else {
            first_limb_check
        }
    };

    let mut inv = 1u64;
    for _ in 0..63 {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(modulus_limbs[0]);
    }
    inv = inv.wrapping_neg();

    let modulus = quote::quote! { #bigint_import([ #( #modulus_limbs ),* ]) };

    let add_with_carry = add_with_carry_impl(limbs);
    let sub_with_borrow = sub_with_borrow_impl(limbs);
    let subtract_modulus = subtract_modulus_impl(&modulus);
    let add_assign = add_assign_impl(modulus_has_spare_bit);
    let double_in_place = double_in_place_impl(modulus_has_spare_bit);
    let mul_assign = mul_assign_impl(
        can_use_no_carry_mul_opt,
        limbs,
        &modulus_limbs,
        modulus_has_spare_bit,
    );
    let square_in_place = square_in_place_impl(
        can_use_no_carry_mul_opt,
        limbs,
        &modulus_limbs,
        modulus_has_spare_bit,
    );
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

    let mut bigint_type: proc_macro2::TokenStream = limb_meta.bigint_type.clone();
    bigint_type.extend(quote::quote! {<#limbs>});

    let mut r_def = quote::quote! {
       const R: B =
    };
    r_def.extend(limb_meta.biguint_macro.clone());
    r_def.extend(quote::quote! {(#r);});

    let mut r2_def = quote::quote! {
       const R2: B =
    };
    r2_def.extend(limb_meta.biguint_macro.clone());
    r2_def.extend(quote::quote! {(#r_squared);});

    quote::quote! {
        const _: () = {
            use ark_ff::{fields::Fp, #bigint_import, BigInteger, biginteger::arithmetic as fa, fields::*};
            type B = #bigint_type;
            type F = Fp<MontBackend<#config_name, #limbs>, #limbs>;

            #[automatically_derived]
            impl MontConfig<#limbs> for #config_name {
                const MODULUS: B = #modulus;

                const GENERATOR: F = ark_ff::MontFp!(#generator);

                const TWO_ADICITY: u32 = #two_adicity;

                const TWO_ADIC_ROOT_OF_UNITY: F = ark_ff::MontFp!(#two_adic_root_of_unity);

                #r_def

                #r2_def

                const INV: u64 = #inv;

                #[doc(hidden)]
                const CAN_USE_NO_CARRY_MUL_OPT: bool = #can_use_no_carry_mul_opt;

                #[doc(hidden)]
                const CAN_USE_NO_CARRY_SQUARE_OPT: bool = #can_use_no_carry_mul_opt;

                #[doc(hidden)]
                const MODULUS_HAS_SPARE_BIT: bool = #modulus_has_spare_bit;


                /// (MODULUS + 1) / 4 when MODULUS % 4 == 3. Used for square root precomputations.
                #[doc(hidden)]
                const MODULUS_PLUS_ONE_DIV_FOUR: Option<B> = #modulus_plus_one_div_four;

                const SQRT_PRECOMP: Option<SqrtPrecomputation<F>> = #sqrt_precomp;

                #mixed_radix

                #[inline(always)]
                fn add_assign(a: &mut F, b: &F) {
                    #add_assign
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
                    #double_in_place
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
                #[inline(always)]
                fn square_in_place(a: &mut F) {
                    #square_in_place
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
        };
    }
}
