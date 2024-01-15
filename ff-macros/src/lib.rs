#![warn(
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    rust_2021_compatibility
)]
#![forbid(unsafe_code)]

use num_bigint::BigUint;
use proc_macro::TokenStream;
use syn::{Expr, ExprLit, Item, ItemFn, Lit, Meta};

mod montgomery;
mod unroll;

pub(crate) mod utils;

#[proc_macro]
pub fn to_sign_and_limbs(input: TokenStream) -> TokenStream {
    let num = utils::parse_string(input).expect("expected decimal string");
    let (is_positive, limbs) = utils::str_to_limbs(&num);

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
pub fn mont_config(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
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

    montgomery::mont_config_helper(
        modulus,
        generator,
        small_subgroup_base,
        small_subgroup_power,
        ast.ident,
    )
    .into()
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
            unroll::unroll_in_block(box_block, unroll_by)
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
    // Go over each attribute
    for attr in attrs {
        match attr.meta {
            // If the attribute's path matches `name`, and if the attribute is of
            // the form `#[name = "value"]`, return `value`
            Meta::NameValue(ref nv) if nv.path.is_ident(name) => {
                // Extract and return the string value.
                // If `value` is not a string, return an error
                if let Expr::Lit(ExprLit {
                    lit: Lit::Str(ref s),
                    ..
                }) = nv.value
                {
                    return Some(s.value());
                } else {
                    panic!("attribute {name} should be a string")
                }
            },
            _ => continue,
        }
    }
    None
}

#[test]
fn test_str_to_limbs() {
    use num_bigint::Sign::*;
    for i in 0..100 {
        for sign in [Plus, Minus] {
            let number = 1i128 << i;
            let signed_number = match sign {
                Minus => -number,
                Plus | _ => number,
            };
            for base in [2, 8, 16, 10] {
                let mut string = match base {
                    2 => format!("{:#b}", number),
                    8 => format!("{:#o}", number),
                    16 => format!("{:#x}", number),
                    10 => format!("{}", number),
                    _ => unreachable!(),
                };
                if sign == Minus {
                    string.insert(0, '-');
                }
                let (is_positive, limbs) = utils::str_to_limbs(&format!("{}", string));
                assert_eq!(
                    limbs[0],
                    format!("{}u64", signed_number.abs() as u64),
                    "{signed_number}, {i}"
                );
                if i > 63 {
                    assert_eq!(
                        limbs[1],
                        format!("{}u64", (signed_number.abs() >> 64) as u64),
                        "{signed_number}, {i}"
                    );
                }

                assert_eq!(is_positive, sign == Plus);
            }
        }
    }
    let (is_positive, limbs) = utils::str_to_limbs("0");
    assert!(is_positive);
    assert_eq!(&limbs, &["0u64".to_string()]);

    let (is_positive, limbs) = utils::str_to_limbs("-5");
    assert!(!is_positive);
    assert_eq!(&limbs, &["5u64".to_string()]);

    let (is_positive, limbs) = utils::str_to_limbs("100");
    assert!(is_positive);
    assert_eq!(&limbs, &["100u64".to_string()]);

    let large_num = -((1i128 << 64) + 101234001234i128);
    let (is_positive, limbs) = utils::str_to_limbs(&large_num.to_string());
    assert!(!is_positive);
    assert_eq!(&limbs, &["101234001234u64".to_string(), "1u64".to_string()]);

    let num = "80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410946";
    let (is_positive, limbs) = utils::str_to_limbs(num);
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
