mod montgomery_backend;
mod standard_backend;
mod utils;

use quote::quote;

pub(crate) fn small_fp_config_helper(
    modulus: u128,
    generator: u128,
    backend: String,
    config_name: proc_macro2::Ident,
) -> proc_macro2::TokenStream {
    let (ty, _suffix) = {
        let u8_max = u128::from(u8::MAX);
        let u16_max = u128::from(u16::MAX);
        let u32_max = u128::from(u32::MAX);
        let u64_max = u128::from(u64::MAX);

        if modulus <= u8_max {
            (quote! { u8 }, "u8")
        } else if modulus <= u16_max {
            (quote! { u16 }, "u16")
        } else if modulus <= u32_max {
            (quote! { u32 }, "u32")
        } else if modulus <= u64_max {
            (quote! { u64 }, "u64")
        } else {
            (quote! { u128 }, "u128")
        }
    };

    let backend_impl = match backend.as_str() {
        "standard" => standard_backend::backend_impl(ty.clone(), modulus, generator),
        "montgomery" => montgomery_backend::backend_impl(ty.clone(), modulus, generator),
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
