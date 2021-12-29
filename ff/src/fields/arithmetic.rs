/// This modular multiplication algorithm uses Montgomery
/// reduction for efficient implementation. It also additionally
/// uses the "no-carry optimization" outlined
/// [here](https://hackmd.io/@zkteam/modular_multiplication) if
/// `P::MODULUS` has (a) a non-zero MSB, and (b) at least one
/// zero bit in the rest of the modulus.
macro_rules! impl_field_mul_assign {
    ($limbs:expr) => {
        #[inline]
        #[ark_ff_asm::unroll_for_loops]
        fn mul_assign(&mut self, other: &Self) {
            // Checking the modulus at compile time
            let first_bit_set = P::MODULUS.0[$limbs - 1] >> 63 != 0;
            // $limbs can be 1, hence we can run into a case with an unused mut.
            #[allow(unused_mut)]
            let mut all_bits_set = P::MODULUS.0[$limbs - 1] == !0 - (1 << 63);
            for i in 1..$limbs {
                all_bits_set &= P::MODULUS.0[$limbs - i - 1] == !0u64;
            }
            let _no_carry: bool = !(first_bit_set || all_bits_set);

            // No-carry optimisation applied to CIOS
            if _no_carry {
                #[cfg(use_asm)]
                #[allow(unsafe_code, unused_mut)]
                {
                    // Tentatively avoid using assembly for `$limbs == 1`.
                    if $limbs <= 6 && $limbs > 1 {
                        ark_ff_asm::x86_64_asm_mul!($limbs, (self.0).0, (other.0).0);
                        self.reduce();
                        return;
                    }
                }
                let mut r = [0u64; $limbs];
                let mut carry1 = 0u64;
                let mut carry2 = 0u64;

                for i in 0..$limbs {
                    r[0] = fa::mac(r[0], input[0], other[i], &mut carry1);
                    let k = r[0].wrapping_mul(P::INV);
                    fa::mac_discard(r[0], k, P::MODULUS.0[0], &mut carry2);
                    for j in 1..$limbs {
                        r[j] = mac_with_carry!(r[j], input[j], other[i], &mut carry1);
                        r[j - 1] = mac_with_carry!(r[j], k, P::MODULUS.0[j], &mut carry2);
                    }
                    r[$limbs - 1] = carry1 + carry2;
                }
                input.copy_from_slice(&r[..]);
            }
        }
    };
}

macro_rules! impl_field_into_repr {
    ($limbs:expr, $BigIntegerType:ty) => {
        #[inline]
        #[ark_ff_asm::unroll_for_loops]
        #[allow(clippy::modulo_one)]
        fn into_repr(&self) -> $BigIntegerType {
            let mut tmp = self.0;
            let mut r = tmp.0;
            // Montgomery Reduction
            for i in 0..$limbs {
                let k = r[i].wrapping_mul(P::INV);
                let mut carry = 0;

                    mac_with_carry!(r[i], k, P::MODULUS.0[0], &mut carry);
                    for j in 1..$limbs {
                        r[(j + i) % $limbs] =
                            mac_with_carry!(r[(j + i) % $limbs], k, P::MODULUS.0[j], &mut carry);
                    }
                    r[i % $limbs] = carry;
                }
                BigInt::<N>(r)
            }
        }
    };
}
// macro_rules! impl_deserialize_flags {
macro_rules! impl_serialize_flags {
    ($limbs: expr) => {
        #[inline]
        #[ark_ff_asm::unroll_for_loops]
        #[allow(unused_braces, clippy::absurd_extreme_comparisons)]
        fn square_in_place(&mut self) -> &mut Self {
            if $limbs == 1 {
                // We default to multiplying with `self` using the `Mul` impl
                // for the 1 limb case
                *self = *self * *self;
                return self;
            }
            #[cfg(use_asm)]
            #[allow(unsafe_code, unused_mut)]
            {
                // Checking the modulus at compile time
                let first_bit_set = P::MODULUS.0[$limbs - 1] >> 63 != 0;
                let mut all_bits_set = P::MODULUS.0[$limbs - 1] == !0 - (1 << 63);
                for i in 1..$limbs {
                    all_bits_set &= P::MODULUS.0[$limbs - i - 1] == core::u64::MAX;
                }
                let _no_carry: bool = !(first_bit_set || all_bits_set);

                if $limbs <= 6 && _no_carry {
                    ark_ff_asm::x86_64_asm_square!($limbs, (self.0).0);
                    self.reduce();
                    return self;
                }
            }
            let mut r = [0u64; $limbs * 2];

// macro_rules! impl_deserialize_flags {
macro_rules! impl_deserialize_flags {
    ($limbs: expr) => {
        paste::paste! {
            fn [<deserialize _id $limbs>]<P: FpParams<N>, R: ark_std::io::Read, F: Flags, const N: usize>(
                mut reader: R,
            ) -> Result<(Fp<P, N>, F), SerializationError> {
                // All reasonable `Flags` should be less than 8 bits in size
                // (256 values are enough for anyone!)
                if F::BIT_SIZE > 8 {
                    return Err(SerializationError::NotEnoughSpace);
                }
                // Calculate the number of bytes required to represent a field element
                // serialized with `flags`. If `F::BIT_SIZE < 8`,
                // this is at most `$byte_size + 1`
                let output_byte_size = buffer_byte_size(P::MODULUS_BITS as usize + F::BIT_SIZE);

                let mut masked_bytes = [0u8; $limbs * 8 + 1];
                reader.read_exact(&mut masked_bytes[..output_byte_size])?;

                let flags = F::from_u8_remove_flags(&mut masked_bytes[output_byte_size - 1])
                    .ok_or(SerializationError::UnexpectedFlags)?;

                Ok((<Fp<P, N>>::read(&masked_bytes[..])?, flags))
            }
        }
    }
}

macro_rules! impl_prime_field_standard_sample {
    ($field: ident, $params: ident) => {
        impl<P: $params> ark_std::rand::distributions::Distribution<$field<P>>
            for ark_std::rand::distributions::Standard
        {
            #[inline]
            fn sample<R: ark_std::rand::Rng + ?Sized>(&self, rng: &mut R) -> $field<P> {
                loop {
                    let mut tmp = $field(
                        rng.sample(ark_std::rand::distributions::Standard),
                        PhantomData,
                    );

                    // Mask away the unused bits at the beginning.
                    assert!(P::REPR_SHAVE_BITS <= 64);
                    let mask = if P::REPR_SHAVE_BITS == 64 {
                        0
                    } else {
                        core::u64::MAX >> P::REPR_SHAVE_BITS
                    };
                    tmp.0.as_mut().last_mut().map(|val| *val &= mask);

                for i in 0..$limbs {
                    r[2 * i] = mac_with_carry!(r[2 * i], input[i], input[i], &mut carry);
                    // need unused assignment because the last iteration of the loop produces an
                    // assignment to `carry` that is unused.
                    #[allow(unused_assignments)]
                    {
                        r[2 * i + 1] = adc!(r[2 * i + 1], 0, &mut carry);
                    }
                }
                // Montgomery reduction
                let mut _carry2 = 0;
                for i in 0..$limbs {
                    let k = r[i].wrapping_mul(P::INV);
                    let mut carry = 0;
                    mac_with_carry!(r[i], k, P::MODULUS.0[0], &mut carry);
                    for j in 1..$limbs {
                        r[j + i] = mac_with_carry!(r[j + i], k, P::MODULUS.0[j], &mut carry);
                    }
                    r[$limbs + i] = adc!(r[$limbs + i], _carry2, &mut carry);
                    _carry2 = carry;
                }
                input.copy_from_slice(&r[N..]);
            }
        }
    };
}

macro_rules! impl_prime_field_from_int {
    ($field: ident, 128, $params: ident, $limbs:expr) => {
        impl<P: $params> From<u128> for $field<P> {
            fn from(other: u128) -> Self {
                let mut default_int = P::BigInt::default();
                if $limbs == 1 {
                    default_int.0[0] = (other % u128::from(P::MODULUS.0[0])) as u64;
                } else {
                    let upper = (other >> 64) as u64;
                    let lower = ((other << 64) >> 64) as u64;
                    // This is equivalent to the following, but satisfying the compiler:
                    // default_int.0[0] = lower;
                    // default_int.0[1] = upper;
                    let limbs = [lower, upper];
                    for (cur, other) in default_int.0.iter_mut().zip(&limbs) {
                        *cur = *other;
                    }
                }
                Self::from_repr(default_int).unwrap()
            }
        }

        impl <P: $params> From<i128> for $field<P> {
            fn from(other: i128) -> Self {
                let abs = Self::from(other.unsigned_abs());
                if other.is_positive() {
                    abs
                } else {
                    -abs
                }
            }
        }
    };
    ($field: ident, bool, $params: ident, $limbs:expr) => {
        impl<P: $params> From<bool> for $field<P> {
            fn from(other: bool) -> Self {
                if $limbs == 1 {
                    Self::from_repr(P::BigInt::from(u64::from(other) % P::MODULUS.0[0])).unwrap()
                } else {
                    Self::from_repr(P::BigInt::from(u64::from(other))).unwrap()
                }
            }
        }
    };
    ($field: ident, $int: expr, $params: ident, $limbs:expr) => {
        paste::paste!{
            impl<P: $params> From<[<u $int>]> for $field<P> {
                fn from(other: [<u $int>]) -> Self {
                    if $limbs == 1 {
                        Self::from_repr(P::BigInt::from(u64::from(other) % P::MODULUS.0[0])).unwrap()
                    } else {
                        Self::from_repr(P::BigInt::from(u64::from(other))).unwrap()
                    }
                }
            }

            impl<P: $params> From<[<i $int>]> for $field<P> {
                fn from(other: [<i $int>]) -> Self {
                    let abs = Self::from(other.unsigned_abs());
                    if other.is_positive() {
                        abs
                    } else {
                        -abs
                    }
                }
            }
        }
    };
}

macro_rules! sqrt_impl {
    ($Self:ident, $P:tt, $self:expr) => {{
        // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)
        // Actually this is just normal Tonelli-Shanks; since `P::Generator`
        // is a quadratic non-residue, `P::ROOT_OF_UNITY = P::GENERATOR ^ t`
        // is also a quadratic non-residue (since `t` is odd).
        if $self.is_zero() {
            return Some($Self::zero());
        }
        // Try computing the square root (x at the end of the algorithm)
        // Check at the end of the algorithm if x was a square root
        // Begin Tonelli-Shanks
        let mut z = $Self::qnr_to_t();
        let mut w = $self.pow($P::T_MINUS_ONE_DIV_TWO);
        let mut x = w * $self;
        let mut b = x * &w;

        let mut v = $P::TWO_ADICITY as usize;

        while !b.is_one() {
            let mut k = 0usize;

            let mut b2k = b;
            while !b2k.is_one() {
                // invariant: b2k = b^(2^k) after entering this loop
                b2k.square_in_place();
                k += 1;
            }

            if k == ($P::TWO_ADICITY as usize) {
                // We are in the case where self^(T * 2^k) = x^(P::MODULUS - 1) = 1,
                // which means that no square root exists.
                return None;
            }
            let j = v - k;
            w = z;
            for _ in 1..j {
                w.square_in_place();
            }

            z = w.square();
            b *= &z;
            x *= &w;
            v = k;
        }
        // Is x the square root? If so, return it.
        if (x.square() == *$self) {
            return Some(x);
        } else {
            // Consistency check that if no square root is found,
            // it is because none exists.
            #[cfg(debug_assertions)]
            {
                use crate::fields::LegendreSymbol::*;
                if ($self.legendre() != QuadraticNonResidue) {
                    panic!("Input has a square root per its legendre symbol, but it was not found")
                }
            }
            None
        }
    }};
}

#[macro_export]
macro_rules! impl_additive_ops_from_ref {
    (<$mod_name:ident> $($args:tt)*) => {
        impl_ops_from_ref!(
            <$mod_name>,
            {
                <add, sub>,
                [sum, zero, add]
            }
            $($args)*
        );
    };
    ($($args:tt)*) => {
        impl_ops_from_ref!(
            <default_ops_mod>,
            {
                <add, sub>,
                [sum, zero, add]
            }
            $($args)*
        );
    };

}

#[macro_export]
macro_rules! impl_ops_from_ref {
    (
        // We define a module, which we have the option to name, to hide the macros
        // to prevent resolution ambiguity, when macro is invoked multiple times
        <$mod_name:ident>,
        // We can here specify the various ops and iter instantiations
        {<$($ops:ident),*>, $([$($iter_args:tt),*]),*}
        // The type we are implementing the ops for
        $type: ident,
        $([
            // These are the type parameters the type is generic over
            $type_params:ident:
            // These are their trait/const generic bounds
            $bounds:ident$(<$($bound_params:tt),*>)?
            // specifically used for const
            $(, $keyword:ident)?

        ]),*

    ) => {
        mod $mod_name {
            use super::*;
            macro_rules! instantiate {
                ($d:tt) => {
                    // Template for instantiating ops
                    macro_rules! ops {
                        (
                            // Name of op
                            $name:ident
                            // lifetime, mutability and ref of other
                            $d(, <$d lifetime:tt $d mut:tt $d deref:tt>)?
                        ) => {
                            paste::paste! {
                                #[allow(unused_qualifications)]
                                impl<
                                    $d($d lifetime, )?
                                    $(
                                        $($keyword)?
                                        $type_params:
                                        $bounds$(<$($bound_params)*>)?
                                    ),*
                                > [<$name:camel>]<$d(&$d lifetime $d mut)?Self> for $type<$($type_params),*>
                                {
                                    type Output = Self;

                                    #[inline]
                                    fn $name(
                                        self,
                                        other: $d(&$d lifetime $d mut)?Self
                                    ) -> Self {
                                        let mut result = self;
                                        result.[<$name:snake _assign>](&$d($d deref)?other);
                                        return result;
                                    }
                                }
                            }
                        }
                    }

                    // Template for instantiating op_assign
                    macro_rules! ops_assign {
                        (
                            // Name of op
                            $name:ident
                            // lifetime, mutability and ref of other
                            $d(, <$d lifetime:tt $d mut:tt $d deref:tt>)?
                        ) => {
                            paste::paste! {
                                #[allow(unused_qualifications)]
                                impl<
                                    $d($d lifetime, )?
                                    $(
                                        $($keyword)?
                                        $type_params:
                                        $bounds$(<$($bound_params)*>)?
                                    ),*
                                > [<$name:camel>]<$d(&$d lifetime $d mut )?Self> for $type<$($type_params),*>
                                {
                                    #[inline]
                                    fn $name(
                                        &mut self,
                                        other: $d(&$d lifetime )?$d($d mut )?Self
                                    ) {
                                        self.$name(&$d($d deref)?other)
                                    }
                                }
                            }
                        }
                    }

                    macro_rules! instantiate_ops {
                        ($d($d op:ident),*) => {
                            paste::paste! {
                                $d(
                                    ops!($d op);
                                    ops!($d op, <'a mut *>);
                                    ops_assign!([<$d op _assign>]);
                                    ops_assign!([<$d op _assign>], <'a mut *>);
                                )*
                            }
                        }
                    }

                    // Template for instantiating product and sum
                    macro_rules! iter {
                        (
                            // Name of iter trait
                            $name:ident,
                            // Name of identity for op
                            $ident:ident,
                            // Name of op
                            $op:ident
                            $d(, <$d lifetime:tt>)?
                        ) => {
                            paste::paste! {
                                #[allow(unused_qualifications)]
                                impl<
                                    $d($d lifetime, )?
                                    $(
                                        $($keyword)?
                                        $type_params:
                                        $bounds$(<$($bound_params)*>)?
                                    ),*
                                > core::iter::[<$name:camel>]<$d(&$d lifetime )?Self> for $type<$($type_params),*>
                                {
                                    fn $name<I: Iterator<Item = $d(&$d lifetime )?Self>>(iter: I) -> Self {
                                        iter.fold(Self::$ident(), [<$op:camel>]::$op)
                                    }
                                }
                            }
                        }
                    }
                }
            }
            instantiate!($);
            instantiate_ops!($($ops),*);
            $(

                iter!($($iter_args),*);
                iter!($($iter_args),*, <'a>);
            )*
        }

        pub use $mod_name::*;
    };
    // We instantiate default module name
    ({$($args0:tt)*}$($args:tt)*) => {
        impl_ops_from_ref!(<default_ops_mod>, {$($args0)*}$($args)*);
    };
    // We instantiate default ops
    ($($args:tt)*) => {
        impl_ops_from_ref!(
            <default_ops_mod>,
            {
                <add, sub, mul, div>,
                [sum, zero, add],
                [product, one, mul]
            }
            $($args)*
        );
    };
}
