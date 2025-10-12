mod montgomery_backend;
mod standard_backend;
mod utils;

use quote::quote;

/// This function is called by the `#[derive(SmallFp)]` macro and generates
/// the implementation of the `SmallFpConfig`
pub(crate) fn small_fp_config_helper(
    modulus: u128,
    generator: u128,
    backend: String,
    config_name: proc_macro2::Ident,
) -> proc_macro2::TokenStream {
    let ty = match modulus {
        m if m < 1u128 << 8 => quote! { u8 },
        m if m < 1u128 << 16 => quote! { u16 },
        m if m < 1u128 << 32 => quote! { u32 },
        m if m < 1u128 << 64 => quote! { u64 },
        _ => quote! { u128 },
    };

    let backend_impl = match backend.as_str() {
        "standard" => standard_backend::backend_impl(&ty, modulus, generator),
        "montgomery" => montgomery_backend::backend_impl(&ty, modulus, generator),
        _ => panic!("Unknown backend type: {}", backend),
    };

    let new_impl = match backend.as_str() {
        "standard" => standard_backend::new(),
        "montgomery" => montgomery_backend::new(modulus, ty),
        _ => panic!("Unknown backend type: {}", backend),
    };

    quote! {
        impl SmallFpConfig for #config_name {
            #backend_impl
        }

        impl #config_name {
            #new_impl
        }
    }
}
