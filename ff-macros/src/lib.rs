#![warn(
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    rust_2021_compatibility
)]
#![forbid(unsafe_code)]

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::One;
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use std::str::FromStr;
use syn::{Expr, Item, ItemFn, Lit};

mod unroll;

fn parse_string(input: TokenStream) -> Option<String> {
    let input: Expr = syn::parse(input).unwrap();
    let input = if let Expr::Group(syn::ExprGroup { expr, .. }) = input {
        expr
    } else {
        panic!("could not parse");
    };
    match *input {
        Expr::Lit(expr_lit) => match expr_lit.lit {
            Lit::Str(s) => Some(s.value()),
            _ => None,
        },
        _ => None,
    }
}

fn str_to_limbs(num: &str) -> (bool, Vec<String>) {
    let (sign, limbs) = str_to_limbs_u64(num);
    (sign, limbs.into_iter().map(|l| format!("{l}u64")).collect())
}

fn str_to_limbs_u64(num: &str) -> (bool, Vec<u64>) {
    let (sign, digits) = BigInt::from_str(num)
        .expect("could not parse to bigint")
        .to_radix_le(16);
    let limbs = digits
        .chunks(16)
        .map(|chunk| {
            let mut this = 0u64;
            for (i, hexit) in chunk.iter().enumerate() {
                this += (*hexit as u64) << (4 * i);
            }
            this
        })
        .collect::<Vec<_>>();

    let sign_is_positive = sign != Sign::Minus;
    (sign_is_positive, limbs)
}

#[proc_macro]
pub fn to_sign_and_limbs(input: TokenStream) -> TokenStream {
    let num = parse_string(input).expect("expected decimal string");
    let (is_positive, limbs) = str_to_limbs(&num);

    let limbs: String = limbs.join(", ");
    let limbs_and_sign = format!("({}", is_positive) + ", [" + &limbs + "])";
    let tuple: Expr = syn::parse_str(&limbs_and_sign).unwrap();
    quote::quote!(#tuple).into()
}

/// Derive the `MontConfig` trait.
///
/// The attributes available to this macro are
/// * `modulus`: Specify the prime modulus underlying this prime field.
/// * `generator`: Specify the generator of the multiplicative subgroup of this
///   prime field. This value must be a quadratic non-residue in the field.
/// * `small_subgroup_base` and `small_subgroup_power` (optional): If the field
///   has insufficient two-adicity, specify an additional subgroup of size
///   `small_subgroup_base.pow(small_subgroup_power)`.
// This code was adapted from the `PrimeField` Derive Macro in ff-derive.
#[proc_macro_derive(
    MontConfig,
    attributes(modulus, generator, small_subgroup_base, small_subgroup_power)
)]
pub fn prime_field(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // Parse the type definition
    let ast: syn::DeriveInput = syn::parse(input).unwrap();

    // We're given the modulus p of the prime field
    let modulus: BigUint = fetch_attr("modulus", &ast.attrs)
        .expect("Please supply a modulus attribute")
        .parse()
        .expect("Modulus should be a number");

    // We may be provided with a generator of p - 1 order. It is required that this
    // generator be quadratic nonresidue.
    let generator: BigUint = fetch_attr("generator", &ast.attrs)
        .expect("Please supply a generator attribute")
        .parse()
        .expect("Generator should be a number");

    let small_subgroup_base: Option<u32> = fetch_attr("small_subgroup_base", &ast.attrs)
        .map(|s| s.parse().expect("small_subgroup_base should be a number"));

    let small_subgroup_power: Option<u32> = fetch_attr("small_subgroup_power", &ast.attrs)
        .map(|s| s.parse().expect("small_subgroup_power should be a number"));

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
    let name = ast.ident;
    let modulus = modulus.to_string();
    let generator = generator.to_string();
    let two_adic_root_of_unity = two_adic_root_of_unity.to_string();
    let modulus_limbs = str_to_limbs_u64(&modulus).1;
    let can_use_no_carry_mul_opt = (*modulus_limbs.last().unwrap() < (u64::MAX >> 1))
        && modulus_limbs[..limbs - 1].iter().any(|l| *l != u64::MAX);
    let modulus = quote::quote! { BigInt([ #( #modulus_limbs ),* ]) };

    let add_with_carry = add_with_carry_impl(limbs);
    let sub_with_borrow = sub_with_borrow_impl(limbs);
    let subtract_modulus = subtract_modulus_impl(&modulus);
    let mul_assign = mul_assign_impl(can_use_no_carry_mul_opt, limbs, &modulus_limbs);

    let mixed_radix = if let Some(large_subgroup_generator) = large_subgroup_generator {
        quote::quote! {
            const SMALL_SUBGROUP_BASE: Option<u32> = Some(#small_subgroup_base);

            const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = Some(#small_subgroup_power);

            const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<F> = Some(ark_ff::MontFp!(#large_subgroup_generator));
        }
    } else {
        quote::quote! {}
    };
    let mod_name = format_ident!("{}___", name.to_string().to_lowercase());
    quote::quote! {
        mod #mod_name {
            use super::#name;
            use ark_ff::{Field, PrimeField, fields::Fp, BigInt, BigInteger, biginteger::arithmetic as fa};
            type B = BigInt<#limbs>;
            type F = Fp<ark_ff::fields::MontBackend<#name, #limbs>, #limbs>;
            #[automatically_derived]
            impl ark_ff::fields::MontConfig<#limbs> for #name {
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
            }

            #subtract_modulus

            #add_with_carry

            #sub_with_borrow
        }
    }
    .into()
}

fn add_with_carry_impl(num_limbs: usize) -> proc_macro2::TokenStream {
    let mut body = proc_macro2::TokenStream::new();
    body.extend(quote! {
        use ark_ff::biginteger::arithmetic::adc_for_add_with_carry as adc;
        let mut carry = 0;
    });
    for i in 0..num_limbs {
        body.extend(quote! {
            carry = adc(&mut a.0[#i], b.0[#i], carry);
        });
    }
    body.extend(quote! {
        carry != 0
    });
    quote! {
        #[inline(always)]
        fn __add_with_carry(
            a: &mut B,
            b: & B,
        ) -> bool {
            #body
        }
    }
    .into()
}

fn sub_with_borrow_impl(num_limbs: usize) -> proc_macro2::TokenStream {
    let mut body = proc_macro2::TokenStream::new();
    body.extend(quote! {
        use ark_ff::biginteger::arithmetic::sbb_for_sub_with_borrow as sbb;
        let mut borrow = 0;
    });
    for i in 0..num_limbs {
        body.extend(quote! {
            borrow = sbb(&mut a.0[#i], b.0[#i], borrow);
        });
    }
    body.extend(quote! {
        borrow != 0
    });
    quote! {
        #[inline(always)]
        fn __sub_with_borrow(
            a: &mut B,
            b: & B,
        ) -> bool {
            #body
        }
    }
    .into()
}

fn subtract_modulus_impl(modulus: &proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    quote! {
        #[inline(always)]
        fn __subtract_modulus(a: &mut F) {
            if a.is_geq_modulus() {
                __sub_with_borrow(&mut a.0, &#modulus);
            }
        }
    }
}

fn mul_assign_impl(
    can_use_no_carry_mul_opt: bool,
    num_limbs: usize,
    modulus_limbs: &[u64],
) -> proc_macro2::TokenStream {
    let mut body = proc_macro2::TokenStream::new();
    let modulus_0 = modulus_limbs[0];
    if can_use_no_carry_mul_opt {
        // This modular multiplication algorithm uses Montgomery
        // reduction for efficient implementation. It also additionally
        // uses the "no-carry optimization" outlined
        // [here](https://hackmd.io/@gnark/modular_multiplication) if
        // `MODULUS` has (a) a non-zero MSB, and (b) at least one
        // zero bit in the rest of the modulus.

        let mut default = proc_macro2::TokenStream::new();
        default.extend(quote! { let mut r = [0u64; #num_limbs]; });
        for i in 0..num_limbs {
            default.extend(quote! {
                let mut carry1 = 0u64;
                r[0] = fa::mac(r[0], (a.0).0[0], (b.0).0[#i], &mut carry1);
                let k = r[0].wrapping_mul(Self::INV);
                let mut carry2 = 0u64;
                fa::mac_discard(r[0], k, #modulus_0, &mut carry2);
            });
            for j in 1..num_limbs {
                let modulus_j = modulus_limbs[j];
                let idx = j - 1;
                default.extend(quote! {
                    r[#j] = fa::mac_with_carry(r[#j], (a.0).0[#j], (b.0).0[#i], &mut carry1);
                    r[#idx] = fa::mac_with_carry(r[#j], k, #modulus_j, &mut carry2);
                });
            }
            default.extend(quote!(r[#num_limbs - 1] = carry1 + carry2;));
        }
        default.extend(quote!((a.0).0 = r;));
        // Avoid using assembly for `N == 1`.
        if (2..=6).contains(&num_limbs) {
            body.extend(quote!({
                if cfg!(all(
                    feature = "asm",
                    target_feature = "bmi2",
                    target_feature = "adx",
                    target_arch = "x86_64"
                )) {
                    #[cfg(
                        all(
                            feature = "asm",
                            target_feature = "bmi2",
                            target_feature = "adx",
                            target_arch = "x86_64"
                        )
                    )]
                    #[allow(unsafe_code, unused_mut)]
                    ark_ff::x86_64_asm_mul!(#num_limbs, (a.0).0, (b.0).0);
                } else {
                    #default
                }
            }))
        } else {
            body.extend(quote!({
                #default
            }))
        }
    } else {
        // We use standard CIOS
        body.extend(quote! {
            let (mut lo, mut hi) = ([0u64; #num_limbs], [0u64; #num_limbs]);
        });
        for i in 0..num_limbs {
            body.extend(quote! { let mut carry = 0; });
            for j in 0..num_limbs {
                let k = i + j;
                if k >= num_limbs {
                    let idx = k - num_limbs;
                    body.extend(quote!{hi[#idx] = fa::mac_with_carry(hi[#idx], (a.0).0[#i], (b.0).0[#j], &mut carry);});
                } else {
                    body.extend(quote!{lo[#k] = fa::mac_with_carry(lo[#k], (a.0).0[#i], (b.0).0[#j], &mut carry);});
                }
                body.extend(quote! { hi[#i] = carry; });
            }
        }
        body.extend(quote!( let mut carry2 = 0; ));
        for i in 0..num_limbs {
            body.extend(quote! {
                let tmp = lo[#i].wrapping_mul(Self::INV);
                let mut carry = 0;
                fa::mac(lo[#i], tmp, #modulus_0, &mut carry);
            });
            for j in 1..num_limbs {
                let modulus_j = modulus_limbs[j];
                let k = i + j;
                if k >= num_limbs {
                    let idx = k - num_limbs;
                    body.extend(quote!(hi[#idx] = fa::mac_with_carry(hi[#idx], tmp, #modulus_j, &mut carry);));
                } else {
                    body.extend(
                        quote!(lo[#k] = fa::mac_with_carry(lo[#k], tmp, modulus_j, &mut carry);),
                    );
                }
                body.extend(quote!(hi[#i] = fa::adc(hi[#i], carry, &mut carry2);));
            }
        }
        body.extend(quote! {
            (a.0).0 = hi;
        });
    }
    body.extend(quote!(__subtract_modulus(a);));
    body
}

const ARG_MSG: &str = "Failed to parse unroll threshold; must be a positive integer";

/// Attribute used to unroll for loops found inside a function block.
#[proc_macro_attribute]
pub fn unroll_for_loops(args: TokenStream, input: TokenStream) -> TokenStream {
    let unroll_by = match syn::parse2::<syn::Lit>(args.into()).expect(ARG_MSG) {
        Lit::Int(int) => int.base10_parse().expect(ARG_MSG),
        _ => panic!("{}", ARG_MSG),
    };

    let item: Item = syn::parse(input).expect("Failed to parse input.");

    if let Item::Fn(item_fn) = item {
        let new_block = {
            let &ItemFn {
                block: ref box_block,
                ..
            } = &item_fn;
            unroll::unroll_in_block(&**box_block, unroll_by)
        };
        let new_item = Item::Fn(ItemFn {
            block: Box::new(new_block),
            ..item_fn
        });
        quote::quote! ( #new_item ).into()
    } else {
        quote::quote! ( #item ).into()
    }
}

/// Fetch an attribute string from the derived struct.
fn fetch_attr(name: &str, attrs: &[syn::Attribute]) -> Option<String> {
    for attr in attrs {
        if let Ok(meta) = attr.parse_meta() {
            match meta {
                syn::Meta::NameValue(nv) => {
                    if nv.path.get_ident().map(|i| i.to_string()) == Some(name.to_string()) {
                        match nv.lit {
                            syn::Lit::Str(ref s) => return Some(s.value()),
                            _ => {
                                panic!("attribute {} should be a string", name);
                            },
                        }
                    }
                },
                _ => {
                    panic!("attribute {} should be a string", name);
                },
            }
        }
    }

    None
}

#[test]
fn test_str_to_limbs() {
    let (is_positive, limbs) = str_to_limbs("-5");
    assert!(!is_positive);
    assert_eq!(&limbs, &["5u64".to_string()]);

    let (is_positive, limbs) = str_to_limbs("100");
    assert!(is_positive);
    assert_eq!(&limbs, &["100u64".to_string()]);

    let large_num = -((1i128 << 64) + 101234001234i128);
    let (is_positive, limbs) = str_to_limbs(&large_num.to_string());
    assert!(!is_positive);
    assert_eq!(&limbs, &["101234001234u64".to_string(), "1u64".to_string()]);

    let num = "80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410946";
    let (is_positive, limbs) = str_to_limbs(num);
    assert!(is_positive);
    let expected_limbs = [
        format!("{}u64", 0x8508c00000000002u64),
        format!("{}u64", 0x452217cc90000000u64),
        format!("{}u64", 0xc5ed1347970dec00u64),
        format!("{}u64", 0x619aaf7d34594aabu64),
        format!("{}u64", 0x9b3af05dd14f6ecu64),
    ];
    assert_eq!(&limbs, &expected_limbs);
}
