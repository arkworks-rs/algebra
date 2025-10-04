use super::*;

// Compute the largest integer `s` such that `N - 1 = 2**s * t` for odd `t`.
pub(crate) const fn compute_two_adicity(modulus: u128) -> u32 {
    assert!(modulus % 2 == 1, "Modulus must be odd");
    assert!(modulus > 1, "Modulus must be greater than 1");

    let mut n_minus_1 = modulus - 1;
    let mut two_adicity = 0;

    while n_minus_1 % 2 == 0 {
        n_minus_1 /= 2;
        two_adicity += 1;
    }
    two_adicity
}

const fn mod_add(x: u128, y: u128, modulus: u128) -> u128 {
    if x >= modulus - y {
        x - (modulus - y)
    } else {
        x + y
    }
}

pub(crate) const fn mod_mul_const(a: u128, b: u128, modulus: u128) -> u128 {
    match a.overflowing_mul(b) {
        (val, false) => val % modulus,
        (_, true) => {
            let mut result = 0u128;
            let mut base = a % modulus;
            let mut exp = b;

            while exp > 0 {
                if exp & 1 == 1 {
                    result = mod_add(result, base, modulus);
                }
                base = mod_add(base, base, modulus);
                exp >>= 1;
            }
            result
        },
    }
}

pub(crate) const fn compute_two_adic_root_of_unity(modulus: u128, two_adicity: u32) -> u128 {
    let qnr = find_quadratic_non_residue(modulus);
    let mut exp = (modulus - 1) >> two_adicity;
    let mut base = qnr % modulus;
    let mut result = 1u128;

    while exp > 0 {
        if exp & 1 == 1 {
            result = mod_mul_const(result, base, modulus);
        }
        base = mod_mul_const(base, base, modulus);
        exp /= 2;
    }
    result
}

const fn pow_mod(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    let mut result = 1;
    base %= modulus;
    while exp > 0 {
        if exp % 2 == 1 {
            result = mod_mul_const(result, base, modulus);
        }
        base = mod_mul_const(base, base, modulus);
        exp /= 2;
    }
    result
}

pub(crate) const fn find_quadratic_non_residue(modulus: u128) -> u128 {
    let exponent = (modulus - 1) / 2;
    let mut z = 2;
    loop {
        let legendre = pow_mod(z, exponent, modulus);
        if legendre == modulus - 1 {
            return z;
        }
        z += 1;
    }
}

pub(crate) fn generate_bigint_casts(
    modulus: u128,
) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    (
        quote! {
            fn from_bigint(a: BigInt<2>) -> Option<SmallFp<Self>> {
                let val = (a.0[0] as u128) + ((a.0[1] as u128) << 64);
                if val > Self::MODULUS_128 {
                    None
                } else {
                    let reduced_val = val % #modulus;
                    Some(SmallFp::new(reduced_val as Self::T))
                }
            }
        },
        quote! {
            fn into_bigint(a: SmallFp<Self>) -> BigInt<2> {
                let val = a.value as u128;
                let lo = val as u64;
                let hi = (val >> 64) as u64;
                ark_ff::BigInt([lo, hi])
            }
        },
    )
}

pub(crate) fn generate_montgomery_bigint_casts(
    modulus: u128,
    _k_bits: u32,
    r_mod_n: u128,
) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    let r2 = mod_mul_const(r_mod_n, r_mod_n, modulus);
    (
        quote! {
            //* Convert from standard representation to Montgomery space
            fn from_bigint(a: BigInt<2>) -> Option<SmallFp<Self>> {
                let val = (a.0[0] as u128) + ((a.0[1] as u128) << 64);
                if val > Self::MODULUS_128 {
                    None
                } else {
                    let reduced_val = val % #modulus;
                    let mut tmp = SmallFp::new(reduced_val as Self::T);
                    let r2_elem = SmallFp::new(#r2 as Self::T);
                    <Self as SmallFpConfig>::mul_assign(&mut tmp, &r2_elem);
                    Some(tmp)
                }
            }
        },
        quote! {
            //* Convert from Montgomery space to standard representation
            fn into_bigint(a: SmallFp<Self>) -> BigInt<2> {
                let mut tmp = a;
                let one = SmallFp::new(1 as Self::T);
                <Self as SmallFpConfig>::mul_assign(&mut tmp, &one);
                let val = tmp.value as u128;
                let lo = val as u64;
                let hi = (val >> 64) as u64;
                ark_ff::BigInt([lo, hi])
            }
        },
    )
}

pub(crate) fn generate_sqrt_precomputation(
    modulus: u128,
    two_adicity: u32,
) -> proc_macro2::TokenStream {
    if modulus % 4 == 3 {
        // Case3Mod4
        let modulus_plus_one_div_four = (modulus + 1) / 4;
        let lo = modulus_plus_one_div_four as u64;
        let hi = (modulus_plus_one_div_four >> 64) as u64;

        quote! {
            const SQRT_PRECOMP: Option<SqrtPrecomputation<SmallFp<Self>>> = {
                const MODULUS_PLUS_ONE_DIV_FOUR: [u64; 2] = [#lo, #hi];
                Some(SqrtPrecomputation::Case3Mod4 {
                    modulus_plus_one_div_four: &MODULUS_PLUS_ONE_DIV_FOUR,
                })
            };
        }
    } else {
        // TonelliShanks
        let trace = (modulus - 1) >> two_adicity;
        // t is od integer division floors to (t-1)/2
        let trace_minus_one_div_two = trace / 2;
        let lo = trace_minus_one_div_two as u64;
        let hi = (trace_minus_one_div_two >> 64) as u64;

        quote! {
            const SQRT_PRECOMP: Option<SqrtPrecomputation<SmallFp<Self>>> = {
                const TRACE_MINUS_ONE_DIV_TWO: [u64; 2] = [#lo, #hi];
                // TWO_ADIC_ROOT_OF_UNITY = g^{(p-1)/2^s} = g^t with odd t
                // ord(g^t) = 2^s, while any square has order at most 2^{s-1}
                // TWO_ADIC_ROOT_OF_UNITY not a square
                Some(SqrtPrecomputation::TonelliShanks {
                    two_adicity: #two_adicity,
                    quadratic_nonresidue_to_trace: Self::TWO_ADIC_ROOT_OF_UNITY,
                    trace_of_modulus_minus_one_div_two: &TRACE_MINUS_ONE_DIV_TWO,
                })
            };
        }
    }
}
