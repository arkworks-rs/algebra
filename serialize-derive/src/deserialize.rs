use crate::serialize::IdentOrIndex;
use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, Index, Type};

fn impl_valid_field(
    check_body: &mut Vec<TokenStream>,
    batch_check_body: &mut Vec<TokenStream>,
    idents: &mut Vec<IdentOrIndex>,
    ty: &Type,
) {
    // Check if type is a tuple.
    match ty {
        Type::Tuple(tuple) => {
            for (i, elem_ty) in tuple.elems.iter().enumerate() {
                let index = Index::from(i);
                idents.push(IdentOrIndex::Index(index));
                impl_valid_field(check_body, batch_check_body, idents, elem_ty);
                idents.pop();
            }
        },
        _ => {
            check_body.push(quote! { ark_serialize::Valid::check(&self.#(#idents).*)?; });
            batch_check_body
                .push(quote! { ark_serialize::Valid::batch_check(batch.iter().map(|v| &v.#(#idents).*))?; });
        },
    }
}

fn impl_valid(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let len = if let Data::Struct(ref data_struct) = ast.data {
        data_struct.fields.len()
    } else {
        panic!(
            "`Valid` can only be derived for structs, {} is not a struct",
            name
        );
    };

    let mut check_body = Vec::<TokenStream>::with_capacity(len);
    let mut batch_body = Vec::<TokenStream>::with_capacity(len);

    match ast.data {
        Data::Struct(ref data_struct) => {
            let mut idents = Vec::<IdentOrIndex>::new();

            for (i, field) in data_struct.fields.iter().enumerate() {
                match field.ident {
                    None => {
                        let index = Index::from(i);
                        idents.push(IdentOrIndex::Index(index));
                    },
                    Some(ref ident) => {
                        idents.push(IdentOrIndex::Ident(ident.clone()));
                    },
                }

                impl_valid_field(&mut check_body, &mut batch_body, &mut idents, &field.ty);

                idents.clear();
            }
        },
        _ => panic!(
            "`Valid` can only be derived for structs, {} is not a struct",
            name
        ),
    };

    let gen = quote! {
        impl #impl_generics ark_serialize::Valid for #name #ty_generics #where_clause {
            #[allow(unused_mut, unused_variables)]
            fn check(&self) -> Result<(), ark_serialize::SerializationError> {
                #(#check_body)*
                Ok(())
            }
            #[allow(unused_mut, unused_variables)]
            fn batch_check<'a>(batch: impl Iterator<Item = &'a Self> + Send) -> Result<(), ark_serialize::SerializationError>
                where
            Self: 'a
            {

                let batch: Vec<_> = batch.collect();
                #(#batch_body)*
                Ok(())
            }
        }
    };
    gen
}

/// Returns a `TokenStream` for `deserialize_with_mode`.
/// uncompressed.
fn impl_deserialize_field(ty: &Type) -> TokenStream {
    // Check if type is a tuple.
    match ty {
        Type::Tuple(tuple) => {
            let compressed_fields: Vec<_> =
                tuple.elems.iter().map(impl_deserialize_field).collect();
            quote! { (#(#compressed_fields)*), }
        },
        _ => {
            quote! { CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?, }
        },
    }
}

pub(super) fn impl_canonical_deserialize(ast: &syn::DeriveInput) -> TokenStream {
    let valid_impl = impl_valid(ast);
    let name = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let deserialize_body;

    match ast.data {
        Data::Struct(ref data_struct) => {
            let mut field_cases = Vec::<TokenStream>::with_capacity(data_struct.fields.len());
            let mut tuple = false;
            for field in data_struct.fields.iter() {
                match &field.ident {
                    None => {
                        tuple = true;
                        let compressed = impl_deserialize_field(&field.ty);
                        field_cases.push(compressed);
                    },
                    // struct field without len_type
                    Some(ident) => {
                        let compressed = impl_deserialize_field(&field.ty);
                        field_cases.push(quote! { #ident: #compressed });
                    },
                }
            }

            deserialize_body = if tuple {
                quote!({
                    Ok(#name (
                        #(#field_cases)*
                     ))
                })
            } else {
                quote!({
                    Ok(#name {
                        #(#field_cases)*
                    })
                })
            };
        },
        _ => panic!(
            "`CanonicalDeserialize` can only be derived for structs, {} is not a Struct",
            name
        ),
    };

    let mut gen = quote! {
        impl #impl_generics CanonicalDeserialize for #name #ty_generics #where_clause {
            #[allow(unused_mut,unused_variables)]
            fn deserialize_with_mode<R: ark_serialize::Read>(
                mut reader: R,
                compress: ark_serialize::Compress,
                validate: ark_serialize::Validate,
            ) -> Result<Self, ark_serialize::SerializationError> {
                #deserialize_body
            }
        }
    };
    gen.extend(valid_impl);
    gen
}
