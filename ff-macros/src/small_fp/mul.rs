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
    let repr_type_str = repr_type.to_string();
    let field_bits = 128 - modulus.leading_zeros();
    let is_mersenne = field_bits >= 2 && modulus == (1u128 << field_bits) - 1;
    let is_babybear = modulus == (1u128 << 31) - (1u128 << 27) + 1;
    let is_koalabear = modulus == (1u128 << 31) - (1u128 << 24) + 1;
    let is_goldilocks = modulus == (1u128 << 64) - (1u128 << 32) + 1;

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

                        let t = (a.value as u64) * (b.value as u64);
                        // k = t * N' can be rewritten using shift
                        //   = t * (2^31 - 2^27 - 1)
                        //   = (t << 31) - (t << 27) - t
                        // mask not needed, montgomery_backend hardcodes R = 2^32 for babybear and koalabear
                        let t_32 = t as u32;
                        let k = (t_32 << 31).wrapping_sub(t_32 << 27).wrapping_sub(t_32) as u64;

                        let kp = (k << 31).wrapping_sub(k << 27).wrapping_add(k);
                        let mut r = t.wrapping_add(kp) >> #k_bits;
                        if r >= MODULUS_MUL_TY { r -= MODULUS_MUL_TY; }
                        a.value = r as u32;
                    }
                }
            } else if is_koalabear {
                // KoalaBear prime
                quote! {
                    #[inline(always)]
                    fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                        const MODULUS_MUL_TY: u64 = #modulus as u64;

                        let t = (a.value as u64) * (b.value as u64);
                        // use same trick as babybear above
                        let t_32 = t as u32;
                        let k = (t_32 << 31).wrapping_sub(t_32 << 24).wrapping_sub(t_32) as u64;

                        let kp = (k << 31).wrapping_sub(k << 24).wrapping_add(k);
                        let mut r = t.wrapping_add(kp) >> #k_bits;
                        if r >= MODULUS_MUL_TY { r -= MODULUS_MUL_TY; }
                        a.value = r as u32;
                    }
                }
            } else {
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
            if is_goldilocks {
                quote! {
                    #[inline(always)]
                    fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
                        // Pornin's reduction copied from winterfell:
                        // https://github.com/facebook/winterfell/blob/main/math/src/field/f64/mod.rs#L714
                        // The referenced paper is https://eprint.iacr.org/2022/274.pdf section 5.1
                        let t  = (a.value as u128) * (b.value as u128);
                        let tl = t as u64;
                        let th = (t >> 64) as u64;

                        let (k, overflow) = tl.overflowing_add(tl << 32);
                        let l = k.wrapping_sub(k >> 32).wrapping_sub(overflow as u64);

                        let (r, overflow) = th.overflowing_sub(l);
                        let mut r = r.wrapping_sub(0u32.wrapping_sub(overflow as u32) as u64);
                        if r >= Self::MODULUS { r -= Self::MODULUS; }
                        a.value = r;
                    }
                }
            } else {
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
            }
        },
    }
}
