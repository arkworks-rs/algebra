use ark_std::{marker::PhantomData, Zero};

use super::{Fp, FpConfig};
use crate::{biginteger::arithmetic as fa, BigInt, BigInteger};
use ark_ff_macros::unroll_for_loops;

/// A trait that specifies the constants and arithmetic procedures
/// for Montgomery arithmetic over the prime field defined by `MODULUS`.
///
/// # Note
/// Manual implementation of this trait is not recommended unless one wishes
/// to specialize arithmetic methods. Instead, the [`MontConfig`][`ark_ff_macros::MontConfig`]
/// derive macro should be used.
pub trait MontConfig<const N: usize>: 'static + Sync + Send + Sized {
    /// The modulus of the field.
    const MODULUS: BigInt<N>;

    /// Let `M` be the power of 2^64 nearest to `Self::MODULUS_BITS`. Then
    /// `R = M % Self::MODULUS`.
    const R: BigInt<N> = Self::MODULUS.montgomery_r();

    /// R2 = R^2 % Self::MODULUS
    const R2: BigInt<N> = Self::MODULUS.montgomery_r2();

    /// INV = -MODULUS^{-1} mod 2^64
    const INV: u64 = inv(&Self::MODULUS);

    /// A multiplicative generator of the field.
    /// `Self::GENERATOR` is an element having multiplicative order
    /// `Self::MODULUS - 1`.
    const GENERATOR: Fp<MontBackend<Self, N>, N>;

    /// Can we use the no-carry optimization for multiplication and squaring
    /// outlined [here](https://hackmd.io/@zkteam/modular_multiplication)?
    ///
    /// This optimization applies if
    /// `Self::MODULUS` has (a) a non-zero MSB, and (b) at least one
    /// zero bit in the rest of the modulus.
    #[doc(hidden)]
    const CAN_USE_NO_CARRY_OPT: bool = can_use_no_carry_optimization(&Self::MODULUS);

    /// 2^s root of unity computed by GENERATOR^t
    const TWO_ADIC_ROOT_OF_UNITY: Fp<MontBackend<Self, N>, N>;

    /// An integer `b` such that there exists a multiplicative subgroup
    /// of size `b^k` for some integer `k`.
    const SMALL_SUBGROUP_BASE: Option<u32> = None;

    /// The integer `k` such that there exists a multiplicative subgroup
    /// of size `Self::SMALL_SUBGROUP_BASE^k`.
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;

    /// GENERATOR^((MODULUS-1) / (2^s *
    /// SMALL_SUBGROUP_BASE^SMALL_SUBGROUP_BASE_ADICITY)).
    /// Used for mixed-radix FFT.
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fp<MontBackend<Self, N>, N>> = None;

    /// Set a += b;
    fn add_assign(a: &mut Fp<MontBackend<Self, N>, N>, b: &Fp<MontBackend<Self, N>, N>) {
        // This cannot exceed the backing capacity.
        a.0.add_with_carry(&b.0);
        // However, it may need to be reduced
        a.subtract_modulus();
    }

    fn sub_assign(a: &mut Fp<MontBackend<Self, N>, N>, b: &Fp<MontBackend<Self, N>, N>) {
        // If `other` is larger than `self`, add the modulus to self first.
        if b.0 > a.0 {
            a.0.add_with_carry(&Self::MODULUS);
        }
        a.0.sub_with_borrow(&b.0);
    }

    fn double_in_place(a: &mut Fp<MontBackend<Self, N>, N>) {
        // This cannot exceed the backing capacity.
        a.0.mul2();
        // However, it may need to be reduced.
        a.subtract_modulus();
    }

    /// This modular multiplication algorithm uses Montgomery
    /// reduction for efficient implementation. It also additionally
    /// uses the "no-carry optimization" outlined
    /// [here](https://hackmd.io/@zkteam/modular_multiplication) if
    /// `Self::MODULUS` has (a) a non-zero MSB, and (b) at least one
    /// zero bit in the rest of the modulus.
    #[inline]
    #[unroll_for_loops(12)]
    fn mul_assign(a: &mut Fp<MontBackend<Self, N>, N>, b: &Fp<MontBackend<Self, N>, N>) {
        // No-carry optimisation applied to CIOS
        if Self::CAN_USE_NO_CARRY_OPT {
            if N <= 6
                && N > 1
                && cfg!(all(
                    feature = "asm",
                    inline_asm_stable,
                    target_feature = "bmi2",
                    target_feature = "adx",
                    target_arch = "x86_64"
                ))
            {
                #[cfg(all(feature = "asm", inline_asm_stable, target_feature = "bmi2", target_feature = "adx", target_arch = "x86_64"))]
                #[allow(unsafe_code, unused_mut)]
                // Tentatively avoid using assembly for `N == 1`.
                #[rustfmt::skip]
                match N {
                    2 => { ark_ff_asm::x86_64_asm_mul!(2, (a.0).0, (b.0).0); },
                    3 => { ark_ff_asm::x86_64_asm_mul!(3, (a.0).0, (b.0).0); },
                    4 => { ark_ff_asm::x86_64_asm_mul!(4, (a.0).0, (b.0).0); },
                    5 => { ark_ff_asm::x86_64_asm_mul!(5, (a.0).0, (b.0).0); },
                    6 => { ark_ff_asm::x86_64_asm_mul!(6, (a.0).0, (b.0).0); },
                    _ => unsafe { ark_std::hint::unreachable_unchecked() },
                };
            } else {
                let mut r = [0u64; N];
                let mut carry1 = 0u64;
                let mut carry2 = 0u64;

                for i in 0..N {
                    r[0] = fa::mac(r[0], (a.0).0[0], (b.0).0[i], &mut carry1);
                    let k = r[0].wrapping_mul(Self::INV);
                    fa::mac_discard(r[0], k, Self::MODULUS.0[0], &mut carry2);
                    for j in 1..N {
                        r[j] = fa::mac_with_carry(r[j], (a.0).0[j], (b.0).0[i], &mut carry1);
                        r[j - 1] = fa::mac_with_carry(r[j], k, Self::MODULUS.0[j], &mut carry2);
                    }
                    r[N - 1] = carry1 + carry2;
                }
                (a.0).0 = r;
            }
        } else {
            // Alternative implementation
            *a = a.mul_without_reduce(b, &Self::MODULUS, Self::INV);
        }
        a.subtract_modulus();
    }

    #[inline]
    #[unroll_for_loops(12)]
    fn square_in_place(a: &mut Fp<MontBackend<Self, N>, N>) {
        if N == 1 {
            // We default to multiplying with `a` using the `Mul` impl
            // for the N == 1 case
            let temp = *a;
            Self::mul_assign(a, &temp);
            return;
        }
        #[cfg(all(
            feature = "asm",
            inline_asm_stable,
            target_feature = "bmi2",
            target_feature = "adx",
            target_arch = "x86_64"
        ))]
        #[allow(unsafe_code, unused_mut)]
        {
            // Checking the modulus at compile time
            if N <= 6 && Self::CAN_USE_NO_CARRY_OPT {
                #[rustfmt::skip]
                match N {
                    2 => { ark_ff_asm::x86_64_asm_square!(2, (a.0).0); },
                    3 => { ark_ff_asm::x86_64_asm_square!(3, (a.0).0); },
                    4 => { ark_ff_asm::x86_64_asm_square!(4, (a.0).0); },
                    5 => { ark_ff_asm::x86_64_asm_square!(5, (a.0).0); },
                    6 => { ark_ff_asm::x86_64_asm_square!(6, (a.0).0); },
                    _ => unsafe { ark_std::hint::unreachable_unchecked() },
                };
                a.subtract_modulus();
                return;
            }
        }
        let mut r = crate::const_helpers::MulBuffer::<N>::zeroed();

        let mut carry = 0;
        for i in 0..(N - 1) {
            for j in (i + 1)..N {
                r[i + j] = fa::mac_with_carry(r[i + j], (a.0).0[i], (a.0).0[j], &mut carry);
            }
            r.b1[i] = carry;
            carry = 0;
        }
        r.b1[N - 1] >>= 63;
        for i in 0..N {
            r[2 * (N - 1) - i] = (r[2 * (N - 1) - i] << 1) | (r[2 * (N - 1) - (i + 1)] >> 63);
        }
        for i in 3..N {
            r[N + 1 - i] = (r[N + 1 - i] << 1) | (r[N - i] >> 63);
        }
        r.b0[1] <<= 1;

        for i in 0..N {
            r[2 * i] = fa::mac_with_carry(r[2 * i], (a.0).0[i], (a.0).0[i], &mut carry);
            r[2 * i + 1] = fa::adc(r[2 * i + 1], 0, &mut carry);
        }
        // Montgomery reduction
        let mut carry2 = 0;
        for i in 0..N {
            let k = r[i].wrapping_mul(Self::INV);
            let mut carry = 0;
            fa::mac_with_carry(r[i], k, Self::MODULUS.0[0], &mut carry);
            for j in 1..N {
                r[j + i] = fa::mac_with_carry(r[j + i], k, Self::MODULUS.0[j], &mut carry);
            }
            r.b1[i] = fa::adc(r.b1[i], carry2, &mut carry);
            carry2 = carry;
        }
        (a.0).0.copy_from_slice(&r.b1);
        a.subtract_modulus();
    }

    fn inverse(a: &Fp<MontBackend<Self, N>, N>) -> Option<Fp<MontBackend<Self, N>, N>> {
        if a.is_zero() {
            None
        } else {
            // Guajardo Kumar Paar Pelzl
            // Efficient Software-Implementation of Finite Fields with Applications to
            // Cryptography
            // Algorithm 16 (BEA for Inversion in Fp)

            let one = BigInt::from(1u64);

            let mut u = a.0;
            let mut v = Self::MODULUS;
            let mut b = Fp::new(Self::R2); // Avoids unnecessary reduction step.
            let mut c = Fp::zero();

            while u != one && v != one {
                while u.is_even() {
                    u.div2();

                    if b.0.is_even() {
                        b.0.div2();
                    } else {
                        b.0.add_with_carry(&Self::MODULUS);
                        b.0.div2();
                    }
                }

                while v.is_even() {
                    v.div2();

                    if c.0.is_even() {
                        c.0.div2();
                    } else {
                        c.0.add_with_carry(&Self::MODULUS);
                        c.0.div2();
                    }
                }

                if v < u {
                    u.sub_with_borrow(&v);
                    b -= &c;
                } else {
                    v.sub_with_borrow(&u);
                    c -= &b;
                }
            }

            if u == one {
                Some(b)
            } else {
                Some(c)
            }
        }
    }

    fn from_bigint(r: BigInt<N>) -> Option<Fp<MontBackend<Self, N>, N>> {
        let mut r = Fp::new(r);
        if r.is_zero() {
            return Some(r);
        } else if r.is_less_than_modulus() {
            r *= &Fp::new(Self::R2);
            Some(r)
        } else {
            None
        }
    }

    #[inline]
    #[unroll_for_loops(12)]
    #[allow(clippy::modulo_one)]
    fn into_bigint(a: Fp<MontBackend<Self, N>, N>) -> BigInt<N> {
        let mut tmp = a.0;
        let mut r = tmp.0;
        // Montgomery Reduction
        for i in 0..N {
            let k = r[i].wrapping_mul(Self::INV);
            let mut carry = 0;

            fa::mac_with_carry(r[i], k, Self::MODULUS.0[0], &mut carry);
            for j in 1..N {
                r[(j + i) % N] =
                    fa::mac_with_carry(r[(j + i) % N], k, Self::MODULUS.0[j], &mut carry);
            }
            r[i % N] = carry;
        }
        tmp.0 = r;
        tmp
    }
}

/// Compute -M^{-1} mod 2^64.
pub const fn inv<const N: usize>(m: &BigInt<N>) -> u64 {
    let mut inv = 1u64;
    crate::const_for!((_i in 0..63) {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(m.0[0]);
    });
    inv.wrapping_neg()
}

#[inline]
pub const fn can_use_no_carry_optimization<const N: usize>(modulus: &BigInt<N>) -> bool {
    // Checking the modulus at compile time
    let first_bit_set = modulus.0[N - 1] >> 63 != 0;
    // N can be 1, hence we can run into a case with an unused mut.
    let mut all_bits_set = modulus.0[N - 1] == !0 - (1 << 63);
    crate::const_for!((i in 1..N) {
        all_bits_set &= modulus.0[N - i - 1] == !0u64;
    });
    !(first_bit_set || all_bits_set)
}

/// Construct a [`Fp<MontBackend<T, N>, N>`] element from a literal string. This should
/// be used primarily for constructing constant field elements; in a non-const
/// context, [`Fp::from_str`](`ark_std::str::FromStr::from_str`) is preferable.
///
/// # Panics
///
/// If the integer represented by the string cannot fit in the number
/// of limbs of the `Fp`, this macro results in a
/// * compile-time error if used in a const context
/// * run-time error otherwise.
///
/// # Usage
///
/// ```rust
/// # use ark_test_curves::{MontFp, One};
/// # use ark_test_curves::bls12_381 as ark_bls12_381;
/// # use ark_std::str::FromStr;
/// use ark_bls12_381::Fq;
/// const ONE: Fq = MontFp!(Fq, "1");
/// const NEG_ONE: Fq = MontFp!(Fq, "-1");
///
/// fn check_correctness() {
///     assert_eq!(ONE, Fq::one());
///     assert_eq!(Fq::from_str("1").unwrap(), ONE);
///     assert_eq!(NEG_ONE, -Fq::one());
/// }
/// ```
#[macro_export]
macro_rules! MontFp {
    ($name:ty, $c0:expr) => {{
        use $crate::PrimeField;
        let (is_positive, limbs) = $crate::ark_ff_macros::to_sign_and_limbs!($c0);
        $crate::Fp::const_from_str(
            &limbs,
            is_positive,
            <$name>::R2,
            &<$name as PrimeField>::MODULUS,
        )
    }};
}

pub use ark_ff_macros::MontConfig;

pub use MontFp;

pub struct MontBackend<T, const N: usize>(PhantomData<T>);

impl<T: MontConfig<N>, const N: usize> FpConfig<N> for MontBackend<T, N> {
    /// The modulus of the field.
    const MODULUS: crate::BigInt<N> = T::MODULUS;

    /// A multiplicative generator of the field.
    /// `Self::GENERATOR` is an element having multiplicative order
    /// `Self::MODULUS - 1`.
    const GENERATOR: Fp<Self, N> = T::GENERATOR;

    /// Additive identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e + f = f`.
    const ZERO: Fp<Self, N> = Fp::new(BigInt([0u64; N]));

    /// Multiplicative identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e * f = f`.
    const ONE: Fp<Self, N> = Fp::new(T::R);

    const TWO_ADICITY: u32 = Self::MODULUS.two_adic_valuation();
    const TWO_ADIC_ROOT_OF_UNITY: Fp<Self, N> = T::TWO_ADIC_ROOT_OF_UNITY;
    const SMALL_SUBGROUP_BASE: Option<u32> = T::SMALL_SUBGROUP_BASE;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = T::SMALL_SUBGROUP_BASE_ADICITY;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fp<Self, N>> = T::LARGE_SUBGROUP_ROOT_OF_UNITY;

    fn add_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        T::add_assign(a, b)
    }

    fn sub_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        T::sub_assign(a, b)
    }

    fn double_in_place(a: &mut Fp<Self, N>) {
        T::double_in_place(a)
    }

    /// This modular multiplication algorithm uses Montgomery
    /// reduction for efficient implementation. It also additionally
    /// uses the "no-carry optimization" outlined
    /// [here](https://hackmd.io/@zkteam/modular_multiplication) if
    /// `P::MODULUS` has (a) a non-zero MSB, and (b) at least one
    /// zero bit in the rest of the modulus.
    #[inline]
    fn mul_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        T::mul_assign(a, b)
    }

    #[inline]
    #[allow(unused_braces, clippy::absurd_extreme_comparisons)]
    fn square_in_place(a: &mut Fp<Self, N>) {
        T::square_in_place(a)
    }

    fn inverse(a: &Fp<Self, N>) -> Option<Fp<Self, N>> {
        T::inverse(a)
    }

    fn from_bigint(r: BigInt<N>) -> Option<Fp<Self, N>> {
        T::from_bigint(r)
    }

    #[inline]
    #[allow(clippy::modulo_one)]
    fn into_bigint(a: Fp<Self, N>) -> BigInt<N> {
        T::into_bigint(a)
    }
}

impl<T, const N: usize> Fp<MontBackend<T, N>, N> {
    const fn const_is_zero(&self) -> bool {
        self.0.const_is_zero()
    }

    #[doc(hidden)]
    const fn const_neg(self, modulus: &BigInt<N>) -> Self {
        if !self.const_is_zero() {
            Self::new(Self::sub_with_borrow(modulus, &self.0))
        } else {
            self
        }
    }

    /// Interpret a string of decimal numbers as a prime field element.
    /// Does not accept unnecessary leading zeroes or a blank string.
    /// For *internal* use only; please use the `ark_ff::MontFp` macro instead
    /// of this method
    #[doc(hidden)]
    pub const fn const_from_str(
        limbs: &[u64],
        is_positive: bool,
        r2: BigInt<N>,
        modulus: &BigInt<N>,
    ) -> Self {
        let mut repr = BigInt::<N>([0; N]);
        assert!(repr.0.len() == N);
        crate::const_for!((i in 0..(limbs.len())) {
            repr.0[i] = limbs[i];
        });
        let res = Self::const_from_bigint(repr, r2, modulus);
        if is_positive {
            res
        } else {
            res.const_neg(modulus)
        }
    }

    #[inline]
    pub(crate) const fn const_from_bigint(
        repr: BigInt<N>,
        r2: BigInt<N>,
        modulus: &BigInt<N>,
    ) -> Self {
        let mut r = Self::new(repr);
        if r.const_is_zero() {
            r
        } else {
            r = r.const_mul(&Fp(r2, PhantomData), modulus);
            r
        }
    }

    const fn mul_without_reduce(mut self, other: &Self, modulus: &BigInt<N>, inv: u64) -> Self {
        let (mut lo, mut hi) = ([0u64; N], [0u64; N]);
        crate::const_for!((i in 0..N) {
            let mut carry = 0;
            crate::const_for!((j in 0..N) {
                let k = i + j;
                if k >= N {
                    hi[k - N] = mac_with_carry!(hi[k - N], (self.0).0[i], (other.0).0[j], &mut carry);
                } else {
                    lo[k] = mac_with_carry!(lo[k], (self.0).0[i], (other.0).0[j], &mut carry);
                }
            });
            hi[i] = carry;
        });
        // Montgomery reduction
        let mut carry2 = 0;
        crate::const_for!((i in 0..N) {
            let tmp = lo[i].wrapping_mul(inv);
            let mut carry = 0;
            mac_with_carry!(lo[i], tmp, modulus.0[0], &mut carry);
            crate::const_for!((j in 1..N) {
                let k = i + j;
                if k >= N {
                    hi[k - N] = mac_with_carry!(hi[k - N], tmp, modulus.0[j], &mut carry);
                }  else {
                    lo[k] = mac_with_carry!(lo[k], tmp, modulus.0[j], &mut carry);
                }
            });
            hi[i] = adc!(hi[i], carry2, &mut carry);
            carry2 = carry;
        });

        crate::const_for!((i in 0..N) {
            (self.0).0[i] = hi[i];
        });
        self
    }

    const fn const_mul_without_reduce(self, other: &Self, modulus: &BigInt<N>) -> Self {
        let inv = inv(modulus);
        self.mul_without_reduce(other, modulus, inv)
    }

    const fn const_mul(mut self, other: &Self, modulus: &BigInt<N>) -> Self {
        self = self.const_mul_without_reduce(other, modulus);
        self.const_reduce(modulus)
    }

    const fn const_is_valid(&self, modulus: &BigInt<N>) -> bool {
        crate::const_for!((i in 0..N) {
            if (self.0).0[(N - i - 1)] < modulus.0[(N - i - 1)] {
                return true
            } else if (self.0).0[(N - i - 1)] > modulus.0[(N - i - 1)] {
                return false
            }
        });
        false
    }

    #[inline]
    const fn const_reduce(mut self, modulus: &BigInt<N>) -> Self {
        if !self.const_is_valid(modulus) {
            self.0 = Self::sub_with_borrow(&self.0, modulus);
        }
        self
    }

    const fn sub_with_borrow(a: &BigInt<N>, b: &BigInt<N>) -> BigInt<N> {
        a.const_sub_with_borrow(b).0
    }
}

impl<T: MontConfig<N>, const N: usize> Fp<MontBackend<T, N>, N> {
    #[doc(hidden)]
    pub const R2: BigInt<N> = T::R2;
    #[doc(hidden)]
    pub const INV: u64 = T::INV;
}
