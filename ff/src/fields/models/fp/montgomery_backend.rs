use ark_std::{marker::PhantomData, Zero};

use super::{Fp, FpConfig};
use crate::{biginteger::arithmetic as fa, BigInt, BigInteger, FftConfig};

/// A trait that defines parameters for a prime field.
pub trait MontConfig<const N: usize>: 'static + Copy + Sync + Send {
    /// The modulus of the field.
    const MODULUS: BigInt<N>;

    /// The number of bits needed to represent the `Self::MODULUS`.
    const MODULUS_BIT_SIZE: u16;

    /// Let `M` be the power of 2^64 nearest to `Self::MODULUS_BITS`. Then
    /// `R = M % Self::MODULUS`.
    const R: BigInt<N>;

    /// R2 = R^2 % Self::MODULUS
    const R2: BigInt<N>;

    /// INV = -MODULUS^{-1} mod 2^64
    const INV: u64;

    /// A multiplicative generator of the field.
    /// `Self::GENERATOR` is an element having multiplicative order
    /// `Self::MODULUS - 1`.
    const GENERATOR: Fp<MontBackend<Self, N>, N>;

    /// The number of bits that can be reliably stored.
    /// (Should equal `SELF::MODULUS_BITS - 1`)
    const CAPACITY: u32;

    /// t for 2^s * t = MODULUS - 1, and t coprime to 2.
    const T: BigInt<N>;

    /// (t - 1) / 2
    const T_MINUS_ONE_DIV_TWO: BigInt<N>;

    /// (Self::MODULUS - 1) / 2
    const MODULUS_MINUS_ONE_DIV_TWO: BigInt<N>;

    /// Let `N` be the size of the multiplicative group defined by the field.
    /// Then `TWO_ADICITY` is the two-adicity of `N`, i.e. the integer `s`
    /// such that `N = 2^s * t` for some odd integer `t`.
    const TWO_ADICITY: u32;

    /// 2^s root of unity computed by GENERATOR^t
    const TWO_ADIC_ROOT_OF_UNITY: Fp<MontBackend<Self, N>, N>;

    /// An integer `b` such that there exists a multiplicative subgroup
    /// of size `b^k` for some integer `k`.
    const SMALL_SUBGROUP_BASE: Option<u32> = None;

    /// The integer `k` such that there exists a multiplicative subgroup
    /// of size `Self::SMALL_SUBGROUP_BASE^k`.
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;

    /// GENERATOR^((MODULUS-1) / (2^s *
    /// SMALL_SUBGROUP_BASE^SMALL_SUBGROUP_BASE_ADICITY)) Used for mixed-radix
    /// FFT.
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fp<MontBackend<Self, N>, N>> = None;
}

pub struct MontBackend<T: MontConfig<N>, const N: usize>(PhantomData<T>);

impl<T: MontConfig<N>, const N: usize> FftConfig for MontBackend<T, N> {
    type Field = Fp<Self, N>;
    const TWO_ADICITY: u32 = T::TWO_ADICITY;
    const TWO_ADIC_ROOT_OF_UNITY: Self::Field = T::TWO_ADIC_ROOT_OF_UNITY;
    const SMALL_SUBGROUP_BASE: Option<u32> = T::SMALL_SUBGROUP_BASE;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = T::SMALL_SUBGROUP_BASE_ADICITY;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self::Field> = T::LARGE_SUBGROUP_ROOT_OF_UNITY;
}

impl<T: MontConfig<N>, const N: usize> FpConfig<N> for MontBackend<T, N> {
    /// The modulus of the field.
    const MODULUS: crate::BigInt<N> = T::MODULUS;

    /// The number of bits needed to represent the `Self::MODULUS`.
    const MODULUS_BIT_SIZE: u16 = T::MODULUS_BIT_SIZE;

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

    /// t for 2^s * t = MODULUS - 1, and t coprime to 2.
    // TODO: compute this directly from `MODULUS`
    const T: crate::BigInt<N> = T::T;

    /// (t - 1) / 2
    // TODO: compute this directly from `T`
    const T_MINUS_ONE_DIV_TWO: crate::BigInt<N> = T::T_MINUS_ONE_DIV_TWO;

    /// (Self::MODULUS - 1) / 2
    // TODO: compute this directly from `MODULUS`
    const MODULUS_MINUS_ONE_DIV_TWO: crate::BigInt<N> = T::MODULUS_MINUS_ONE_DIV_TWO;

    /// Set a += b;
    fn add_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        // This cannot exceed the backing capacity.
        a.0.add_nocarry(&b.0);
        // However, it may need to be reduced
        a.reduce();
    }

    fn sub_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        // If `other` is larger than `self`, add the modulus to self first.
        if b.0 > a.0 {
            a.0.add_nocarry(&Self::MODULUS);
        }
        a.0.sub_noborrow(&b.0);
    }

    fn double_in_place(a: &mut Fp<Self, N>) {
        // This cannot exceed the backing capacity.
        a.0.mul2();
        // However, it may need to be reduced.
        a.reduce();
    }

    /// This modular multiplication algorithm uses Montgomery
    /// reduction for efficient implementation. It also additionally
    /// uses the "no-carry optimization" outlined
    /// [here](https://hackmd.io/@zkteam/modular_multiplication) if
    /// `P::MODULUS` has (a) a non-zero MSB, and (b) at least one
    /// zero bit in the rest of the modulus.
    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    fn mul_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        // Checking the modulus at compile time
        let first_bit_set = T::MODULUS.0[N - 1] >> 63 != 0;
        // N can be 1, hence we can run into a case with an unused mut.
        #[allow(unused_mut)]
        let mut all_bits_set = T::MODULUS.0[N - 1] == !0 - (1 << 63);
        for i in 1..N {
            all_bits_set &= T::MODULUS.0[N - i - 1] == !0u64;
        }
        let no_carry = !(first_bit_set || all_bits_set);

        // No-carry optimisation applied to CIOS
        if no_carry {
            #[cfg(use_asm)]
            #[allow(unsafe_code, unused_mut)]
            {
                // Tentatively avoid using assembly for `$limbs == 1`.
                if N <= 6 && N > 1 {
                    ark_ff_asm::x86_64_asm_mul!($limbs, (a.0).0, (b.0).0);
                    self.reduce();
                    return;
                }
            }
            let mut r = [0u64; N];
            let mut carry1 = 0u64;
            let mut carry2 = 0u64;

            for i in 0..N {
                r[0] = fa::mac(r[0], (a.0).0[0], (b.0).0[i], &mut carry1);
                let k = r[0].wrapping_mul(T::INV);
                fa::mac_discard(r[0], k, T::MODULUS.0[0], &mut carry2);
                for j in 1..N {
                    r[j] = fa::mac_with_carry(r[j], (a.0).0[j], (b.0).0[i], &mut carry1);
                    r[j - 1] = fa::mac_with_carry(r[j], k, T::MODULUS.0[j], &mut carry2);
                }
                r[N - 1] = carry1 + carry2;
            }
            (a.0).0 = r;
            a.reduce();
        // Alternative implementation
        } else {
            *a = a.mul_without_reduce(b, T::MODULUS, T::INV);
            a.reduce();
        }
    }

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    #[allow(unused_braces, clippy::absurd_extreme_comparisons)]
    fn square_in_place(a: &mut Fp<Self, N>) {
        if N == 1 {
            // We default to multiplying with `a` using the `Mul` impl
            // for the N == 1 case
            Self::mul_assign(a, &*a);
            return;
        }
        #[cfg(use_asm)]
        #[allow(unsafe_code, unused_mut)]
        {
            // Checking the modulus at compile time
            let first_bit_set = T::MODULUS.0[N - 1] >> 63 != 0;
            let mut all_bits_set = T::MODULUS.0[N - 1] == !0 - (1 << 63);
            for i in 1..N {
                all_bits_set &= T::MODULUS.0[N - i - 1] == core::u64::MAX;
            }
            let no_carry: bool = !(first_bit_set || all_bits_set);

            if N <= 6 && no_carry {
                ark_ff_asm::x86_64_asm_square!(N, (a.0).0);
                a.reduce();
                return a;
            }
        }
        let mut r = super::buffer_helpers::MulBuffer::new([0u64; N], [0u64; N]);

        let mut carry = 0;
        for i in 0..N {
            if i < N - 1 {
                for j in 0..N {
                    if j > i {
                        r[i + j] = fa::mac_with_carry(r[i + j], (a.0).0[i], (a.0).0[j], &mut carry);
                    }
                }
                r.b1[i] = carry;
                carry = 0;
            }
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
            // need unused assignment because the last iteration of the loop produces an
            // assignment to `carry` that is unused.
            #[allow(unused_assignments)]
            {
                r[2 * i + 1] = fa::adc(r[2 * i + 1], 0, &mut carry);
            }
        }
        // Montgomery reduction
        let mut _carry2 = 0;
        for i in 0..N {
            let k = r[i].wrapping_mul(T::INV);
            let mut carry = 0;
            fa::mac_with_carry(r[i], k, T::MODULUS.0[0], &mut carry);
            for j in 1..N {
                r[j + i] = fa::mac_with_carry(r[j + i], k, T::MODULUS.0[j], &mut carry);
            }
            r.b1[i] = fa::adc(r.b1[i], _carry2, &mut carry);
            _carry2 = carry;
        }
        (a.0).0.copy_from_slice(&r.b1);
        a.reduce();
    }

    fn inverse(a: &Fp<Self, N>) -> Option<Fp<Self, N>> {
        if a.is_zero() {
            None
        } else {
            // Guajardo Kumar Paar Pelzl
            // Efficient Software-Implementation of Finite Fields with Applications to
            // Cryptography
            // Algorithm 16 (BEA for Inversion in Fp)

            let one = BigInt::from(1u64);

            let mut u = a.0;
            let mut v = T::MODULUS;
            let mut b = Fp::new(T::R2); // Avoids unnecessary reduction step.
            let mut c = Fp::zero();

            while u != one && v != one {
                while u.is_even() {
                    u.div2();

                    if b.0.is_even() {
                        b.0.div2();
                    } else {
                        b.0.add_nocarry(&T::MODULUS);
                        b.0.div2();
                    }
                }

                while v.is_even() {
                    v.div2();

                    if c.0.is_even() {
                        c.0.div2();
                    } else {
                        c.0.add_nocarry(&T::MODULUS);
                        c.0.div2();
                    }
                }

                if v < u {
                    u.sub_noborrow(&v);
                    b -= &c;
                } else {
                    v.sub_noborrow(&u);
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

    fn from_bigint(r: BigInt<N>) -> Option<Fp<Self, N>> {
        let mut r = Fp::new(r);
        if r.is_zero() {
            return Some(r);
        } else if r.is_valid() {
            r *= &Fp::new(T::R2);
            Some(r)
        } else {
            None
        }
    }

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    #[allow(clippy::modulo_one)]
    fn into_bigint(a: Fp<Self, N>) -> BigInt<N> {
        let mut tmp = a.0;
        let mut r = tmp.0;
        // Montgomery Reduction
        for i in 0..N {
            let k = r[i].wrapping_mul(T::INV);
            let mut carry = 0;

            fa::mac_with_carry(r[i], k, T::MODULUS.0[0], &mut carry);
            for j in 1..N {
                r[(j + i) % N] = fa::mac_with_carry(r[(j + i) % N], k, T::MODULUS.0[j], &mut carry);
            }
            r[i % N] = carry;
        }
        tmp.0 = r;
        tmp
    }
}

impl<T: MontConfig<N>, const N: usize> Fp<MontBackend<T, N>, N> {
    #[ark_ff_asm::unroll_for_loops]
    const fn const_is_zero(&self) -> bool {
        let mut is_zero = true;
        crate::for_loop!((i in 0..N) {
            is_zero &= (self.0).0[i] == 0;
        });
        is_zero
    }

    const fn const_neg(self, modulus: BigInt<N>) -> Self {
        if !self.const_is_zero() {
            Self::new(Self::sub_noborrow(&modulus, &self.0))
        } else {
            self
        }
    }

    /// Interpret a string of decimal numbers as a prime field element.
    /// Does not accept unnecessary leading zeroes or a blank string.
    /// For *internal* use only; please use the `field_new` macro instead
    /// of this method
    #[doc(hidden)]
    pub const fn const_from_str(
        limbs: &[u64],
        is_positive: bool,
        r2: BigInt<N>,
        modulus: BigInt<N>,
        inv: u64,
    ) -> Self {
        let mut repr = BigInt::<N>([0; N]);
        crate::for_loop!((i in 0..(limbs.len())) {
            repr.0[i] = limbs[i];
        });
        let res = Self::const_from_bigint(repr, r2, modulus, inv);
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
        modulus: BigInt<N>,
        inv: u64,
    ) -> Self {
        let mut r = Self::new(repr);
        if r.const_is_zero() {
            r
        } else {
            r = r.const_mul(&Fp(r2, PhantomData), modulus, inv);
            r
        }
    }

    #[ark_ff_asm::unroll_for_loops]
    const fn mul_without_reduce(mut self, other: &Self, modulus: BigInt<N>, inv: u64) -> Self {
        use crate::biginteger::arithmetic as fa;

        let mut r = super::buffer_helpers::MulBuffer::zeroed();

        crate::for_loop!((i in 0..N) {
            let mut carry = 0;
            crate::for_loop!((j in 0..N) {
                *r.get_mut(j + i) = fa::mac_with_carry(*r.get(j + i), (self.0).0[i], (other.0).0[j], &mut carry);
            });
            r.b1[i] = carry;
            i += 1;

        });
        // Montgomery reduction
        let mut _carry2 = 0;
        crate::for_loop!((i in 0..N) {
            let k = r.b0[i].wrapping_mul(inv);
            let mut carry = 0;
            fa::mac_with_carry(r.b0[i], k, modulus.0[0], &mut carry);
            crate::for_loop!((j in 1..N) {
                *r.get_mut(j + i) = fa::mac_with_carry(*r.get(j + i), k, modulus.0[j], &mut carry);
            });
            r.b1[i] = fa::adc(r.b1[i], _carry2, &mut carry);
            _carry2 = carry;
        });

        crate::for_loop!((i in 0..N) {
            (self.0).0[i] = r.b1[i];
        });
        self
    }

    #[ark_ff_asm::unroll_for_loops]
    const fn const_mul(mut self, other: &Self, modulus: BigInt<N>, inv: u64) -> Self {
        self = self.mul_without_reduce(other, modulus, inv);
        self.const_reduce(modulus)
    }

    #[ark_ff_asm::unroll_for_loops]
    const fn const_is_valid(&self, modulus: BigInt<N>) -> bool {
        crate::for_loop!((i in 0..N) {
            if (self.0).0[(N - i - 1)] < modulus.0[(N - i - 1)] {
                return true
            } else if (self.0).0[(N - i - 1)] > modulus.0[(N - i - 1)] {
                return false
            }
        });
        false
    }

    #[inline]
    const fn const_reduce(mut self, modulus: BigInt<N>) -> Self {
        if !self.const_is_valid(modulus) {
            self.0 = Self::sub_noborrow(&self.0, &modulus);
        }
        self
    }

    #[ark_ff_asm::unroll_for_loops]
    // need unused assignment because the last iteration of the loop produces an assignment
    // to `borrow` that is unused.
    #[allow(unused_assignments)]
    const fn sub_noborrow(a: &BigInt<N>, b: &BigInt<N>) -> BigInt<N> {
        use crate::biginteger::arithmetic::sbb;
        let mut a = *a;
        let mut borrow = 0;
        crate::for_loop!((i in 0..N) {
            a.0[i] = sbb(a.0[i], b.0[i], &mut borrow);
        });
        a
    }
}
