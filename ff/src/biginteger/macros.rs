macro_rules! bigint_impl {
    ($name:ident, $num_limbs:expr) => {
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Default, Hash, Zeroize)]
        pub struct $name(pub [u64; $num_limbs]);

        impl $name {
            pub const fn new(value: [u64; $num_limbs]) -> Self {
                $name(value)
            }
        }

        impl BigInteger for $name {
            const NUM_LIMBS: usize = $num_limbs;

            #[inline]
            #[ark_ff_asm::unroll_for_loops]
            fn add_nocarry(&mut self, other: &Self) -> bool {
                let mut carry = 0;

                for i in 0..$num_limbs {
                    #[cfg(all(target_arch = "x86_64", feature = "asm"))]
                    #[allow(unsafe_code)]
                    unsafe {
                        use core::arch::x86_64::_addcarry_u64;
                        carry = _addcarry_u64(carry, self.0[i], other.0[i], &mut self.0[i])
                    };

                    #[cfg(not(all(target_arch = "x86_64", feature = "asm")))]
                    {
                        self.0[i] = adc!(self.0[i], other.0[i], &mut carry);
                    }
                }

                carry != 0
            }

            #[inline]
            #[ark_ff_asm::unroll_for_loops]
            fn sub_noborrow(&mut self, other: &Self) -> bool {
                let mut borrow = 0;

                for i in 0..$num_limbs {
                    #[cfg(all(target_arch = "x86_64", feature = "asm"))]
                    #[allow(unsafe_code)]
                    unsafe {
                        use core::arch::x86_64::_subborrow_u64;
                        borrow = _subborrow_u64(borrow, self.0[i], other.0[i], &mut self.0[i])
                    };

                    #[cfg(not(all(target_arch = "x86_64", feature = "asm")))]
                    {
                        self.0[i] = sbb!(self.0[i], other.0[i], &mut borrow);
                    }
                }

                borrow != 0
            }

            #[inline]
            #[ark_ff_asm::unroll_for_loops]
            #[allow(unused)]
            fn mul2(&mut self) {
                #[cfg(all(target_arch = "x86_64", feature = "asm"))]
                #[allow(unsafe_code)]
                {
                    let mut carry = 0;

                    for i in 0..$num_limbs {
                        unsafe {
                            use core::arch::x86_64::_addcarry_u64;
                            carry = _addcarry_u64(carry, self.0[i], self.0[i], &mut self.0[i])
                        };
                    }
                }

                #[cfg(not(all(target_arch = "x86_64", feature = "asm")))]
                {
                    let mut last = 0;
                    for i in 0..$num_limbs {
                        let a = &mut self.0[i];
                        let tmp = *a >> 63;
                        *a <<= 1;
                        *a |= last;
                        last = tmp;
                    }
                }
            }

            #[inline]
            #[ark_ff_asm::unroll_for_loops]
            fn muln(&mut self, mut n: u32) {
                if n >= 64 * $num_limbs {
                    *self = Self::from(0);
                    return;
                }

                while n >= 64 {
                    let mut t = 0;
                    for i in 0..$num_limbs {
                        core::mem::swap(&mut t, &mut self.0[i]);
                    }
                    n -= 64;
                }

                if n > 0 {
                    let mut t = 0;
                    #[allow(unused)]
                    for i in 0..$num_limbs {
                        let a = &mut self.0[i];
                        let t2 = *a >> (64 - n);
                        *a <<= n;
                        *a |= t;
                        t = t2;
                    }
                }
            }

            #[inline]
            #[ark_ff_asm::unroll_for_loops]
            #[allow(unused)]
            fn div2(&mut self) {
                let mut t = 0;
                for i in 0..$num_limbs {
                    let a = &mut self.0[$num_limbs - i - 1];
                    let t2 = *a << 63;
                    *a >>= 1;
                    *a |= t;
                    t = t2;
                }
            }

            #[inline]
            #[ark_ff_asm::unroll_for_loops]
            fn divn(&mut self, mut n: u32) {
                if n >= 64 * $num_limbs {
                    *self = Self::from(0);
                    return;
                }

                while n >= 64 {
                    let mut t = 0;
                    for i in 0..$num_limbs {
                        core::mem::swap(&mut t, &mut self.0[$num_limbs - i - 1]);
                    }
                    n -= 64;
                }

                if n > 0 {
                    let mut t = 0;
                    #[allow(unused)]
                    for i in 0..$num_limbs {
                        let a = &mut self.0[$num_limbs - i - 1];
                        let t2 = *a << (64 - n);
                        *a >>= n;
                        *a |= t;
                        t = t2;
                    }
                }
            }

            #[inline]
            fn is_odd(&self) -> bool {
                self.0[0] & 1 == 1
            }

            #[inline]
            fn is_even(&self) -> bool {
                !self.is_odd()
            }

            #[inline]
            fn is_zero(&self) -> bool {
                for i in 0..$num_limbs {
                    if self.0[i] != 0 {
                        return false;
                    }
                }
                true
            }

            #[inline]
            fn num_bits(&self) -> u32 {
                let mut ret = $num_limbs * 64;
                for i in self.0.iter().rev() {
                    let leading = i.leading_zeros();
                    ret -= leading;
                    if leading != 64 {
                        break;
                    }
                }

                ret
            }

            #[inline]
            fn get_bit(&self, i: usize) -> bool {
                if i >= 64 * $num_limbs {
                    false
                } else {
                    let limb = i / 64;
                    let bit = i - (64 * limb);
                    (self.0[limb] & (1 << bit)) != 0
                }
            }

            #[inline]
            fn from_bits_be(bits: &[bool]) -> Self {
                let mut res = Self::default();
                let mut acc: u64 = 0;

                let mut bits = bits.to_vec();
                bits.reverse();
                for (i, bits64) in bits.chunks(64).enumerate() {
                    for bit in bits64.iter().rev() {
                        acc <<= 1;
                        acc += *bit as u64;
                    }
                    res.0[i] = acc;
                    acc = 0;
                }
                res
            }

            fn from_bits_le(bits: &[bool]) -> Self {
                let mut res = Self::default();
                let mut acc: u64 = 0;

                let bits = bits.to_vec();
                for (i, bits64) in bits.chunks(64).enumerate() {
                    for bit in bits64.iter().rev() {
                        acc <<= 1;
                        acc += *bit as u64;
                    }
                    res.0[i] = acc;
                    acc = 0;
                }
                res
            }

            #[inline]
            fn to_bytes_be(&self) -> Vec<u8> {
                let mut le_bytes = self.to_bytes_le();
                le_bytes.reverse();
                le_bytes
            }

            #[inline]
            fn to_bytes_le(&self) -> Vec<u8> {
                let array_map = self.0.iter().map(|limb| limb.to_le_bytes());
                let mut res = Vec::<u8>::with_capacity($num_limbs * 8);
                for limb in array_map {
                    res.extend_from_slice(&limb);
                }
                res
            }

            #[inline]
            fn find_wnaf(&self) -> Vec<i64> {
                let mut res = vec![];

                let mut e = self.clone();
                while !e.is_zero() {
                    let z: i64;
                    if e.is_odd() {
                        z = 2 - (e.0[0] % 4) as i64;
                        if z >= 0 {
                            e.sub_noborrow(&Self::from(z as u64));
                        } else {
                            e.add_nocarry(&Self::from((-z) as u64));
                        }
                    } else {
                        z = 0;
                    }
                    res.push(z);
                    e.div2();
                }

                res
            }
        }

        impl CanonicalSerialize for $name {
            #[inline]
            fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
                self.write(writer)?;
                Ok(())
            }

            #[inline]
            fn serialized_size(&self) -> usize {
                Self::NUM_LIMBS * 8
            }
        }

        impl CanonicalDeserialize for $name {
            #[inline]
            fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
                let value = Self::read(reader)?;
                Ok(value)
            }
        }

        impl ToBytes for $name {
            #[inline]
            fn write<W: Write>(&self, writer: W) -> IoResult<()> {
                self.0.write(writer)
            }
        }

        impl FromBytes for $name {
            #[inline]
            fn read<R: Read>(reader: R) -> IoResult<Self> {
                <[u64; $num_limbs]>::read(reader).map(Self::new)
            }
        }

        impl Display for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                for i in self.0.iter().rev() {
                    write!(f, "{:016X}", *i)?;
                }
                Ok(())
            }
        }

        impl Ord for $name {
            #[inline]
            #[ark_ff_asm::unroll_for_loops]
            fn cmp(&self, other: &Self) -> ::core::cmp::Ordering {
                use core::cmp::Ordering;
                for i in 0..$num_limbs {
                    let a = &self.0[$num_limbs - i - 1];
                    let b = &other.0[$num_limbs - i - 1];
                    if a < b {
                        return Ordering::Less;
                    } else if a > b {
                        return Ordering::Greater;
                    }
                }
                Ordering::Equal
            }
        }

        impl PartialOrd for $name {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<::core::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Distribution<$name> for Standard {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $name {
                $name(rng.gen())
            }
        }

        impl AsMut<[u64]> for $name {
            #[inline]
            fn as_mut(&mut self) -> &mut [u64] {
                &mut self.0
            }
        }

        impl AsRef<[u64]> for $name {
            #[inline]
            fn as_ref(&self) -> &[u64] {
                &self.0
            }
        }

        impl From<u64> for $name {
            #[inline]
            fn from(val: u64) -> $name {
                let mut repr = Self::default();
                repr.0[0] = val;
                repr
            }
        }
    };
}
