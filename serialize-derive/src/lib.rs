#![warn(
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    rust_2021_compatibility
)]
#![forbid(unsafe_code)]

use syn::{parse_macro_input, DeriveInput};

mod serialize;
use serialize::*;

mod deserialize;
use deserialize::*;

#[proc_macro_derive(CanonicalSerialize)]
pub fn derive_canonical_serialize(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    proc_macro::TokenStream::from(impl_canonical_serialize(&ast))
}

#[proc_macro_derive(CanonicalDeserialize)]
pub fn derive_canonical_deserialize(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    proc_macro::TokenStream::from(impl_canonical_deserialize(&ast))
}
