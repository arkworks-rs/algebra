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

const fn mod_add_const(x: u128, y: u128, modulus: u128) -> u128 {
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
                    result = mod_add_const(result, base, modulus);
                }
                base = mod_add_const(base, base, modulus);
                exp >>= 1;
            }
            result
        },
    }
}

const fn pow_mod_const(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
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

pub(crate) const fn compute_two_adic_root_of_unity(
    modulus: u128,
    two_adicity: u32,
    generator: u128,
) -> u128 {
    let exp = (modulus - 1) >> two_adicity;
    let base = generator % modulus;
    pow_mod_const(base, exp, modulus)
}

// Finds smallest quadratic non-residue by using Euler's criterion
pub(crate) const fn find_quadratic_non_residue(modulus: u128) -> u128 {
    let exponent = (modulus - 1) / 2;
    let mut z = 2;
    loop {
        let legendre = pow_mod_const(z, exponent, modulus);
        if legendre == modulus - 1 {
            return z;
        }
        z += 1;
    }
}

pub(crate) fn generate_montgomery_bigint_casts(
) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    (
        quote! {
            fn from_bigint(a: ark_ff::BigInt<1>) -> Option<SmallFp<Self>> {
                let val = a.0[0] as u128;
                if val >= Self::MODULUS_U128 {
                    None
                } else {
                    let val_t = Self::T::try_from(val).ok().unwrap();
                    Some(Self::new(val_t))
                }
            }
        },
        quote! {
            fn into_bigint(a: SmallFp<Self>) -> ark_ff::BigInt<1> {
                let mut tmp = a;
                let one = SmallFp::from_raw(1 as Self::T);
                Self::mul_assign(&mut tmp, &one);
                let val = tmp.value as u128;
                ark_ff::BigInt([val as u64])
            }
        },
    )
}

pub(crate) fn generate_sqrt_precomputation(
    modulus: u128,
    two_adicity: u32,
    r_mod_n: Option<u128>,
) -> proc_macro2::TokenStream {
    if modulus % 4 == 3 {
        let modulus_plus_one_div_four = (modulus + 1) / 4;
        let lo = modulus_plus_one_div_four as u64;

        quote! {
            // Case3Mod4 square root precomputation
            const SQRT_PRECOMP: Option<ark_ff::SqrtPrecomputation<SmallFp<Self>>> = {
                const MODULUS_PLUS_ONE_DIV_FOUR: [u64; 1] = [#lo];
                Some(ark_ff::SqrtPrecomputation::Case3Mod4 {
                    modulus_plus_one_div_four: &MODULUS_PLUS_ONE_DIV_FOUR,
                })
            };
        }
    } else {
        let trace = (modulus - 1) >> two_adicity;
        let trace_minus_one_div_two = trace / 2;
        let lo = trace_minus_one_div_two as u64;
        let qnr = find_quadratic_non_residue(modulus);
        let qnr_to_trace = match r_mod_n {
            None => pow_mod_const(qnr, trace, modulus),
            Some(reduced) => mod_mul_const(pow_mod_const(qnr, trace, modulus), reduced, modulus),
        };

        quote! {
            // TonelliShanks square root precomputation
            const SQRT_PRECOMP: Option<ark_ff::SqrtPrecomputation<SmallFp<Self>>> = {
                const TRACE_MINUS_ONE_DIV_TWO: [u64; 1] = [#lo];
                Some(ark_ff::SqrtPrecomputation::TonelliShanks {
                    two_adicity: #two_adicity,
                    quadratic_nonresidue_to_trace: SmallFp::from_raw(#qnr_to_trace as Self::T),
                    trace_of_modulus_minus_one_div_two: &TRACE_MINUS_ONE_DIV_TWO,
                })
            };
        }
    }
}
