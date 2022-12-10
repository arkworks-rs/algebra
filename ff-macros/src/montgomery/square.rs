use quote::quote;

pub(super) fn square_in_place_impl(
    can_use_no_carry_mul_opt: bool,
    num_limbs: usize,
    modulus_limbs: &[u64],
    modulus_has_spare_bit: bool,
) -> proc_macro2::TokenStream {
    let mut body = proc_macro2::TokenStream::new();
    let mut default = proc_macro2::TokenStream::new();

    let modulus_0 = modulus_limbs[0];
    let double_num_limbs = 2 * num_limbs;
    default.extend(quote! {
        let mut r = [0u64; #double_num_limbs];
        let mut carry = 0;
    });
    for i in 0..(num_limbs - 1) {
        for j in (i + 1)..num_limbs {
            default.extend(quote! {
                r[#i + #j] = fa::mac_with_carry(r[#i + #j], (a.0).0[#i], (a.0).0[#j], &mut carry);
            })
        }
        default.extend(quote! {
            r[#num_limbs + #i] = carry;
            carry = 0;
        });
    }
    default.extend(quote! { r[#double_num_limbs - 1] = r[#double_num_limbs - 2] >> 63; });
    for i in 2..(double_num_limbs - 1) {
        default.extend(quote! {
            r[#double_num_limbs - #i] =
            (r[#double_num_limbs - #i] << 1) | (r[#double_num_limbs - (#i + 1)] >> 63);
        });
    }
    default.extend(quote! { r[1] <<= 1; });

    for i in 0..num_limbs {
        default.extend(quote! {
            r[2 * #i] = fa::mac_with_carry(r[2 * #i], (a.0).0[#i], (a.0).0[#i], &mut carry);
            carry = fa::adc(&mut r[2 * #i + 1], 0, carry);
        });
    }
    // Montgomery reduction
    default.extend(quote! { let mut carry2 = 0; });
    for i in 0..num_limbs {
        default.extend(quote! {
            let k = r[#i].wrapping_mul(Self::INV);
            let mut carry = 0;
            fa::mac_discard(r[#i], k, #modulus_0, &mut carry);
        });
        for j in 1..num_limbs {
            let idx = j + i;
            let modulus_j = modulus_limbs[j];
            default.extend(quote! {
                r[#idx] = fa::mac_with_carry(r[#idx], k, #modulus_j, &mut carry);
            });
        }
        default.extend(quote! { carry2 = fa::adc(&mut r[#num_limbs + #i], carry, carry2); });
    }
    default.extend(quote! { (a.0).0 = r[#num_limbs..].try_into().unwrap(); });

    if num_limbs == 1 {
        // We default to multiplying with `a` using the `Mul` impl
        // for the N == 1 case
        return quote!({
            *a *= *a;
        });
    } else if (2..=6).contains(&num_limbs) && can_use_no_carry_mul_opt {
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
                {
                    ark_ff::x86_64_asm_square!(#num_limbs, (a.0).0);
                    __subtract_modulus(a);
                }
            } else {
                #default
                __subtract_modulus(a);
            }
        }));
        return body;
    } else {
        body.extend(quote!( #default ));
        if modulus_has_spare_bit {
            body.extend(quote!(__subtract_modulus(a);));
        } else {
            body.extend(quote!(__subtract_modulus_with_carry(a, carry2 != 0);));
        }
    }
    body
}
