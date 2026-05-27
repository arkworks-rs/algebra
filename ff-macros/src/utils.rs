use std::str::FromStr;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{Num, Zero};
use proc_macro::TokenStream;
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};
use syn::parse::{Parse, ParseStream};
use syn::{Expr, Lit, Token};

pub(crate) struct FieldArgs {
    pub modulus: String,
    pub generator: String,
    pub name: Ident,
}

impl Parse for FieldArgs {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let mut modulus: Option<String> = None;
        let mut generator: Option<String> = None;
        let mut name: Option<Ident> = None;

        while !input.is_empty() {
            let key: Ident = input.parse()?;
            input.parse::<Token![=]>()?;

            match key.to_string().as_str() {
                "modulus" => {
                    let lit: syn::LitStr = input.parse()?;
                    modulus = Some(lit.value());
                },
                "generator" => {
                    let lit: syn::LitStr = input.parse()?;
                    generator = Some(lit.value());
                },
                "name" => {
                    if input.peek(syn::LitStr) {
                        let lit: syn::LitStr = input.parse()?;
                        name = Some(Ident::new(&lit.value(), Span::call_site()));
                    } else {
                        name = Some(input.parse()?);
                    }
                },
                _ => {
                    return Err(syn::Error::new(
                        key.span(),
                        "unknown argument; expected one of: modulus, generator, name",
                    ))
                },
            }

            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
        }

        Ok(Self {
            modulus: modulus.ok_or_else(|| {
                syn::Error::new(Span::call_site(), "missing required argument: modulus")
            })?,
            generator: generator.ok_or_else(|| {
                syn::Error::new(Span::call_site(), "missing required argument: generator")
            })?,
            name: name.ok_or_else(|| {
                syn::Error::new(Span::call_site(), "missing required argument: name")
            })?,
        })
    }
}

pub(crate) fn fp_alias_for_limbs(limbs: usize) -> TokenStream2 {
    match limbs {
        1 => quote::quote!(ark_ff::Fp64),
        2 => quote::quote!(ark_ff::Fp128),
        3 => quote::quote!(ark_ff::Fp192),
        4 => quote::quote!(ark_ff::Fp256),
        5 => quote::quote!(ark_ff::Fp320),
        6 => quote::quote!(ark_ff::Fp384),
        7 => quote::quote!(ark_ff::Fp448),
        8 => quote::quote!(ark_ff::Fp512),
        9 => quote::quote!(ark_ff::Fp576),
        10 => quote::quote!(ark_ff::Fp640),
        11 => quote::quote!(ark_ff::Fp704),
        12 => quote::quote!(ark_ff::Fp768),
        13 => quote::quote!(ark_ff::Fp832),
        _ => panic!("unsupported field size: {limbs} limbs (supported range is 1..=13)"),
    }
}

pub(crate) fn parse_string(input: TokenStream) -> Option<String> {
    let mut input: Expr = syn::parse(input).unwrap();
    // Unwrap invisible group delimiters that the compiler may (or may not)
    // insert around tokens forwarded from other proc macros.
    if let Expr::Group(syn::ExprGroup { expr, .. }) = input {
        input = *expr;
    }
    match input {
        Expr::Lit(expr_lit) => match expr_lit.lit {
            Lit::Str(s) => Some(s.value()),
            _ => None,
        },
        _ => None,
    }
}

/// Detect a small prime subgroup of the multiplicative group.
///
/// Checks whether any small prime base in {3, 5, 7} divides the odd part of
/// p-1 at least once. Returns the smallest such `(base, adicity)` if found,
/// or `None` if the odd part has no factors ≤ 7.
pub(crate) fn find_conservative_subgroup_base(modulus: &BigUint) -> Option<(u32, u32)> {
    let mut trace = modulus - BigUint::from(1u32);
    while trace.bit(0) == false {
        trace >>= 1u32;
    }

    for b in [3u32, 5, 7] {
        let base = BigUint::from(b);
        let mut t = trace.clone();
        let mut adicity = 0u32;
        while (&t % &base).is_zero() {
            t /= &base;
            adicity += 1;
        }
        if adicity > 0 {
            return Some((b, adicity));
        }
    }

    None
}

pub(crate) fn str_to_limbs(num: &str) -> (bool, Vec<String>) {
    let (sign, limbs) = str_to_limbs_u64(num);
    (sign, limbs.into_iter().map(|l| format!("{l}u64")).collect())
}

pub(crate) fn str_to_limbs_u64(num: &str) -> (bool, Vec<u64>) {
    let is_negative = num.starts_with('-');
    let num = if is_negative { &num[1..] } else { num };
    let number = if num.starts_with("0x") || num.starts_with("0X") {
        // We are in hexadecimal
        BigInt::from_str_radix(&num[2..], 16)
    } else if num.starts_with("0o") || num.starts_with("0O") {
        // We are in octal
        BigInt::from_str_radix(&num[2..], 8)
    } else if num.starts_with("0b") || num.starts_with("0B") {
        // We are in binary
        BigInt::from_str_radix(&num[2..], 2)
    } else {
        // We are in decimal
        BigInt::from_str(num)
    }
    .expect("could not parse to bigint");
    let number = if is_negative { -number } else { number };
    let (sign, digits) = number.to_radix_le(16);

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
