use std::str::FromStr;

use num_bigint::{BigInt, Sign};
use num_traits::Num;
use proc_macro::TokenStream;
use syn::{Expr, Lit};

pub fn parse_string(input: TokenStream) -> Option<String> {
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

pub fn str_to_limbs(num: &str) -> (bool, Vec<String>) {
    let (sign, limbs) = str_to_limbs_u64(num);
    (sign, limbs.into_iter().map(|l| format!("{l}u64")).collect())
}

pub fn str_to_limbs_u64(num: &str) -> (bool, Vec<u64>) {
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
