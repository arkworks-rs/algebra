use super::*;
use crate::small_fp::utils::{
    compute_two_adic_root_of_unity, compute_two_adicity, generate_montgomery_bigint_casts,
    generate_sqrt_precomputation, mod_mul_const,
};

pub(crate) fn backend_impl(
    ty: proc_macro2::TokenStream,
    modulus: u128,
    generator: u128,
) -> proc_macro2::TokenStream {
    let k_bits = 128 - modulus.leading_zeros();
    let r: u128 = 1u128 << k_bits;
    let r_mod_n = r % modulus;
    let r_mask = r - 1;

    let n_prime = mod_inverse_pow2(modulus, k_bits);
    let one_mont = r_mod_n;
    let generator_mont = mod_mul_const(generator % modulus, r_mod_n % modulus, modulus);

    let two_adicity = compute_two_adicity(modulus);
    let two_adic_root = compute_two_adic_root_of_unity(modulus, two_adicity);
    let two_adic_root_mont = mod_mul_const(two_adic_root, r_mod_n, modulus);

    let neg_one_mont = mod_mul_const(modulus - 1, r_mod_n, modulus);

    let (from_bigint_impl, into_bigint_impl) =
        generate_montgomery_bigint_casts(modulus, k_bits, r_mod_n);
    let sqrt_precomp_impl = generate_sqrt_precomputation(modulus, two_adicity);

    quote! {
        type T = #ty;
        const MODULUS: Self::T = #modulus as Self::T;
        const MODULUS_128: u128 = #modulus;
        const GENERATOR: SmallFp<Self> = SmallFp::new(#generator_mont as Self::T);
        const ZERO: SmallFp<Self> = SmallFp::new(0 as Self::T);
        const ONE: SmallFp<Self> = SmallFp::new(#one_mont as Self::T);
        const NEG_ONE: SmallFp<Self> = SmallFp::new(#neg_one_mont as Self::T);


        const TWO_ADICITY: u32 = #two_adicity;
        const TWO_ADIC_ROOT_OF_UNITY: SmallFp<Self> = SmallFp::new(#two_adic_root_mont as Self::T);
        #sqrt_precomp_impl

        fn add_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            a.value = match a.value.overflowing_add(b.value) {
                (val, false) => val % Self::MODULUS,
                (val, true) => (Self::T::MAX - Self::MODULUS + 1 + val) % Self::MODULUS,
            };
        }

        fn sub_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            if a.value >= b.value {
                a.value -= b.value;
            } else {
                a.value = Self::MODULUS - (b.value - a.value);
            }
        }

        fn double_in_place(a: &mut SmallFp<Self>) {
            let tmp = *a;
            Self::add_assign(a, &tmp);
        }

        fn neg_in_place(a: &mut SmallFp<Self>) {
            if a.value != (0 as Self::T) {
                a.value = Self::MODULUS - a.value;
            }
        }

        fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            let a_u128 = a.value as u128;
            let b_u128 = b.value as u128;

            let a_lo = a_u128 as u64;
            let a_hi = (a_u128 >> 64) as u64;
            let b_lo = b_u128 as u64;
            let b_hi = (b_u128 >> 64) as u64;

            // t = a * b (256-bit result stored as t_lo, t_hi)
            let lolo = (a_lo as u128) * (b_lo as u128);
            let lohi = (a_lo as u128) * (b_hi as u128);
            let hilo = (a_hi as u128) * (b_lo as u128);
            let hihi = (a_hi as u128) * (b_hi as u128);

            let (cross_sum, cross_carry) = lohi.overflowing_add(hilo);
            let (mid, mid_carry) = lolo.overflowing_add(cross_sum << 64);
            let t_lo = mid;
            let t_hi = hihi + (cross_sum >> 64) + ((cross_carry as u128) << 64) + (mid_carry as u128);

            // m = t_lo * n_prime & r_mask
            let m = t_lo.wrapping_mul(#n_prime) & #r_mask;

            // mn = m * modulus
            let m_lo = m as u64;
            let m_hi = (m >> 64) as u64;
            let n_lo = #modulus as u64;
            let n_hi = (#modulus >> 64) as u64;

            let lolo = (m_lo as u128) * (n_lo as u128);
            let lohi = (m_lo as u128) * (n_hi as u128);
            let hilo = (m_hi as u128) * (n_lo as u128);
            let hihi = (m_hi as u128) * (n_hi as u128);

            let (cross_sum, cross_carry) = lohi.overflowing_add(hilo);
            let (mid, mid_carry) = lolo.overflowing_add(cross_sum << 64);
            let mn_lo = mid;
            let mn_hi = hihi + (cross_sum >> 64) + ((cross_carry as u128) << 64) + (mid_carry as u128);

            // (t + mn) / R
            let (sum_lo, carry) = t_lo.overflowing_add(mn_lo);
            let sum_hi = t_hi + mn_hi + (carry as u128);

            let mut u = if #k_bits < 128 {
                (sum_lo >> #k_bits) | (sum_hi << (128 - #k_bits))
            } else {
                sum_hi >> (#k_bits - 128)
            };

            if u >= #modulus {
                u -= #modulus;
            }
            a.value = u as Self::T;
        }

        fn sum_of_products<const T: usize>(
            a: &[SmallFp<Self>; T],
            b: &[SmallFp<Self>; T],) -> SmallFp<Self> {
            let mut acc = SmallFp::new(0 as Self::T);
            for (x, y) in a.iter().zip(b.iter()) {
                let mut prod = *x;
                Self::mul_assign(&mut prod, y);
                Self::add_assign(&mut acc, &prod);
            }
            acc
        }

        fn square_in_place(a: &mut SmallFp<Self>) {
            let tmp = *a;
            Self::mul_assign(a, &tmp);
        }

        fn inverse(a: &SmallFp<Self>) -> Option<SmallFp<Self>> {
            if a.value == 0 {
                return None;
            }

            let mut result = Self::ONE;
            let mut base = *a;
            let mut exp = Self::MODULUS - 2;

            while exp > 0 {
                if exp & 1 == 1 {
                    Self::mul_assign(&mut result, &base);
                }

                let mut sq = base;
                Self::mul_assign(&mut sq, &base);
                base = sq;
                exp >>= 1;
            }

            Some(result)
        }

        #from_bigint_impl

        #into_bigint_impl
    }
}

fn mod_inverse_pow2(n: u128, bits: u32) -> u128 {
    let mut inv = 1u128;
    for _ in 0..bits {
        inv = inv.wrapping_mul(2u128.wrapping_sub(n.wrapping_mul(inv)));
    }
    inv.wrapping_neg()
}

pub(crate) fn new(modulus: u128, _ty: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let k_bits = 128 - modulus.leading_zeros();
    let r: u128 = 1u128 << k_bits;
    let r_mod_n = r % modulus;
    let r2 = mod_mul_const(r_mod_n, r_mod_n, modulus);

    quote! {
        pub fn new(value: <Self as SmallFpConfig>::T) -> SmallFp<Self> {
            let reduced_value = value % <Self as SmallFpConfig>::MODULUS;
            let mut tmp = SmallFp::new(reduced_value);
            let r2_elem = SmallFp::new(#r2 as <Self as SmallFpConfig>::T);
            <Self as SmallFpConfig>::mul_assign(&mut tmp, &r2_elem);
            tmp
        }

        pub fn exit(a: &mut SmallFp<Self>) {
            let mut tmp = *a;
            let one = SmallFp::new(1 as <Self as SmallFpConfig>::T);
            <Self as SmallFpConfig>::mul_assign(&mut tmp, &one);
            a.value = tmp.value;
        }
    }
}
