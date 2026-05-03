use quote::quote;

// Generates the mul_assign implementation at compile time including a few
// optimized paths
pub(crate) fn generate_mul_impl(
    repr_type: &proc_macro2::TokenStream,
    modulus: u128,
    k_bits: u32,
    r_mask: u128,
    n_prime: u128,
) -> proc_macro2::TokenStream {
    const BABYBEAR_PRIME: u128 = 2013265921; // 2^31 - 2^27 + 1
    const KOALABEAR_PRIME: u128 = 2130706433; // 2^31 - 2^24 + 1
    const GOLDILOCKS_PRIME: u128 = 18446744069414584321; // 2^64 - 2^32 + 1

    let repr_type_str = repr_type.to_string();
    let field_bits = 128 - modulus.leading_zeros();
    let is_mersenne = field_bits >= 2 && modulus == (1u128 << field_bits) - 1;
    let is_babybear = modulus == BABYBEAR_PRIME;
    let is_koalabear = modulus == KOALABEAR_PRIME;
    let is_goldilocks = modulus == GOLDILOCKS_PRIME;
    
    // Wider type for the product: u8→u16, u16→u32, u32→u64
    let mul_ty = match repr_type_str.as_str() {
        "u8" => quote! { u16 },
        "u16" => quote! { u32 },
        "u32" => quote! { u64 },
        _ => quote! { u128 },
    };

    match (repr_type_str.as_str(), is_mersenne) {
        ("u8" | "u16", false) => {
            // All (non-mersenne) primes < 2^16
            quote! {
                #[inline(always)]
                fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                    const MODULUS_MUL_TY: #mul_ty = #modulus as #mul_ty;
                    const N_PRIME: #repr_type = #n_prime as #repr_type;
                    const MASK: #mul_ty = #r_mask as #mul_ty;
                    const K_BITS: u32 = #k_bits;

                    let tmp = (a.value as #mul_ty) * (b.value as #mul_ty);
                    let carry1 = (tmp >> K_BITS) as #repr_type;
                    let r = (tmp & MASK) as #repr_type;
                    let m = r.wrapping_mul(N_PRIME);
                    let tmp = (r as #mul_ty) + ((m as #mul_ty) * MODULUS_MUL_TY);
                    let carry2 = (tmp >> K_BITS) as #repr_type;
                    let mut r = (carry1 as #mul_ty) + (carry2 as #mul_ty);
                    if r >= MODULUS_MUL_TY { r -= MODULUS_MUL_TY; }
                    a.value = r as #repr_type;
                }
            }
        },
        ("u8" | "u16" | "u32", true) => {
            // All mersenne primes < 2^32
            // skips montgomery, uses direct reduction
            quote! {
                #[inline(always)]
                fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                    const K: u32 = #field_bits;
                    const MODULUS: #mul_ty = #modulus as #mul_ty;
                    let prod = (a.value as #mul_ty) * (b.value as #mul_ty);
                    let mut r = (prod & MODULUS) + (prod >> K);
                    if r >= MODULUS { r -= MODULUS; }
                    a.value = r as #repr_type;
                }
            }
        },
        ("u32", false) => {
            if is_babybear {
                // BabyBear prime
                quote! {
                    #[inline(always)]
                    fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                        const MODULUS_MUL_TY: u64 = #modulus as u64;
                        const N_PRIME: u64 = #n_prime as u64;
                        const R_MASK: u64 = #r_mask as u64;
    
                        let t = (a.value as u64) * (b.value as u64);
                        let k = t.wrapping_mul(N_PRIME) & R_MASK;

                        let kp = (k << 31).wrapping_sub(k << 27).wrapping_add(k);
                        let mut r = t.wrapping_add(kp) >> #k_bits;
                        if r >= MODULUS_MUL_TY { r -= MODULUS_MUL_TY; }
                        a.value = r as u32;
                    }
                }
            }
            else if is_koalabear {
                // KoalaBear prime
                quote! {
                    #[inline(always)]
                    fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                        const MODULUS_MUL_TY: u64 = #modulus as u64;
                        const N_PRIME: u64 = #n_prime as u64;
                        const R_MASK: u64 = #r_mask as u64;
    
                        let t = (a.value as u64) * (b.value as u64);
                        let k = t.wrapping_mul(N_PRIME) & R_MASK;

                        let kp = (k << 31).wrapping_sub(k << 24).wrapping_add(k);
                        let mut r = t.wrapping_add(kp) >> #k_bits;
                        if r >= MODULUS_MUL_TY { r -= MODULUS_MUL_TY; }
                        a.value = r as u32;
                    }
                } 
            }
            else {
                // Primes where 2^16 < p < 2^32
                quote! {
                    #[inline(always)]
                    fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                        const MODULUS_MUL_TY: u64 = #modulus as u64;
                        const N_PRIME: u64 = #n_prime as u64;
                        const R_MASK: u64 = #r_mask as u64;
    
                        let t = (a.value as u64) * (b.value as u64);
                        let k = t.wrapping_mul(N_PRIME) & R_MASK;
                        let mut r = (t + (k * MODULUS_MUL_TY)) >> #k_bits;
                        if r >= MODULUS_MUL_TY { r -= MODULUS_MUL_TY; }
                        a.value = r as u32;
                    }
                }
            }
        },
        _ => {
            // Goldilocks, others < 2^64
            let shift_bits = 128 - k_bits;
            quote! {
                #[inline(always)]
                fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                    const MODULUS_MUL_TY: u128 = #modulus as u128;
                    const N_PRIME: u128 = #n_prime as u128;
                    const R_MASK: u128 = #r_mask as u128;

                    let mut t = (a.value as u128) * (b.value as u128);
                    let k = t.wrapping_mul(N_PRIME) & R_MASK;
                    let (t, overflow) = t.overflowing_add(k * MODULUS_MUL_TY);
                    let mut r = (t >> #k_bits) + ((overflow as u128) << #shift_bits);
                    if r >= MODULUS_MUL_TY { r -= MODULUS_MUL_TY; }
                    a.value = r as u64;
                }
            }
        },
    }
}