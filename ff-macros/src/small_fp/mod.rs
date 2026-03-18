mod montgomery_backend;
mod utils;

use quote::quote;

/// This function is called by the `#[derive(SmallFp)]` macro and generates
/// the implementation of the `SmallFpConfig`
pub(crate) fn small_fp_config_helper(
    modulus: u128,
    generator: u128,
    config_name: proc_macro2::Ident,
) -> proc_macro2::TokenStream {
    let ty = match modulus {
        m if m < 1u128 << 8 => quote! { u8 },
        m if m < 1u128 << 16 => quote! { u16 },
        m if m < 1u128 << 32 => quote! { u32 },
        m if m < 1u128 << 64 => quote! { u64 },
        _ => quote! { u128 },
    };

    assert!(modulus < 1u128 << 127,
        "SmallFpConfig montgomery backend supports only moduli < 2^127. Use MontConfig with BigInt instead of SmallFp."
    );

    let backend_impl = montgomery_backend::backend_impl(&ty, modulus, generator);
    let exit_impl = montgomery_backend::exit_impl();

    quote! {
        const _: () = {
            use ark_ff::{SmallFp, SmallFpConfig};

            impl SmallFpConfig for #config_name {
                #backend_impl
            }

            impl #config_name {
                #exit_impl
            }
        };
    }
}
