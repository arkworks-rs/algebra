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
            format!("{}u64", this)
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
    if let Some(large_subgroup_generator) = large_subgroup_generator {
        quote::quote! {
            #[automatically_derived]
            impl ark_ff::fields::MontConfig<#limbs> for #name {

                const MODULUS: ark_ff::BigInt<#limbs> = ark_ff::BigInt!(#modulus);

                const GENERATOR: ark_ff::fields::Fp<ark_ff::fields::MontBackend<Self, #limbs>, #limbs> = ark_ff::MontFp!(#generator);

                const TWO_ADIC_ROOT_OF_UNITY: ark_ff::fields::Fp<ark_ff::fields::MontBackend<Self, #limbs>, #limbs> = ark_ff::MontFp!(#two_adic_root_of_unity);

                const SMALL_SUBGROUP_BASE: Option<u32> = Some(#small_subgroup_base);

                const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = Some(#small_subgroup_power);

                const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<ark_ff::fields::Fp<ark_ff::fields::MontBackend<Self, #limbs>, #limbs>> = Some(ark_ff::MontFp!(#large_subgroup_generator));
            }
        }
    } else {
        quote::quote! {
            #[automatically_derived]
            impl ark_ff::fields::MontConfig<#limbs> for #name {

                const MODULUS: ark_ff::BigInt<#limbs> = ark_ff::BigInt!(#modulus);

                const GENERATOR: ark_ff::fields::Fp<ark_ff::fields::MontBackend<Self, #limbs>, #limbs> = ark_ff::MontFp!(#generator);

                const TWO_ADIC_ROOT_OF_UNITY: ark_ff::fields::Fp<ark_ff::fields::MontBackend<Self, #limbs>, #limbs> = ark_ff::MontFp!(#two_adic_root_of_unity);
            }
        }
    }.into()
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
