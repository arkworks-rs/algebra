use ark_std::ops::{Index, IndexMut};

/// A helper macro for emulating `for` loops in a `const` context.
///
/// # Usage
/// ```rust
/// # use ark_ff::const_for;
/// const fn for_in_const() {
///     let mut array = [0usize; 4];
///     const_for!((i in 0..(array.len())) { // We need to wrap the `array.len()` in parenthesis.
///         array[i] = i;
///     });
///     assert!(array[0] == 0);
///     assert!(array[1] == 1);
///     assert!(array[2] == 2);
///     assert!(array[3] == 3);
/// }
/// ```
#[macro_export]
macro_rules! const_for {
    (($i:ident in $start:tt..$end:tt)  $code:expr ) => {{
        let mut $i = $start;
        while $i < $end {
            $code
            $i += 1;
        }
    }};
}

/// A buffer to hold values of size 2 * N. This is mostly
/// a hack that's necessary until `generic_const_exprs` is stable.
#[derive(Copy, Clone)]
#[repr(C, align(8))]
pub(super) struct MulBuffer<const N: usize> {
    pub(super) b0: [u64; N],
    pub(super) b1: [u64; N],
}

impl<const N: usize> MulBuffer<N> {
    const fn new(b0: [u64; N], b1: [u64; N]) -> Self {
        Self { b0, b1 }
    }

    pub(super) const fn zeroed() -> Self {
        let b = [0u64; N];
        Self::new(b, b)
    }

    #[inline(always)]
    pub(super) const fn get(&self, index: usize) -> &u64 {
        if index < N {
            &self.b0[index]
        } else {
            &self.b1[index - N]
        }
    }

    #[inline(always)]
    pub(super) fn get_mut(&mut self, index: usize) -> &mut u64 {
        if index < N {
            &mut self.b0[index]
        } else {
            &mut self.b1[index - N]
        }
    }
}

impl<const N: usize> Index<usize> for MulBuffer<N> {
    type Output = u64;
    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index)
    }
}

impl<const N: usize> IndexMut<usize> for MulBuffer<N> {
    #[inline(always)]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index)
    }
}

pub(super) struct RBuffer<const N: usize>(pub [u64; N], pub u64);

impl<const N: usize> RBuffer<N> {
    /// Find the number of bits in the binary decomposition of `self`.
    pub(super) const fn num_bits(&self) -> u32 {
        (N * 64) as u32 + (64 - self.1.leading_zeros())
    }

    /// Returns the `i`-th bit where bit 0 is the least significant one.
    /// In other words, the bit with weight `2^i`.
    pub(super) const fn get_bit(&self, i: usize) -> bool {
        let d = i / 64;
        let b = i % 64;
        if d == N {
            (self.1 >> b) & 1 == 1
        } else {
            (self.0[d] >> b) & 1 == 1
        }
    }
}

pub(super) struct R2Buffer<const N: usize>(pub [u64; N], pub [u64; N], pub u64);

impl<const N: usize> R2Buffer<N> {
    /// Find the number of bits in the binary decomposition of `self`.
    pub(super) const fn num_bits(&self) -> u32 {
        ((2 * N) * 64) as u32 + (64 - self.2.leading_zeros())
    }

    /// Returns the `i`-th bit where bit 0 is the least significant one.
    /// In other words, the bit with weight `2^i`.
    pub(super) const fn get_bit(&self, i: usize) -> bool {
        let d = i / 64;
        let b = i % 64;
        if d == 2 * N {
            (self.2 >> b) & 1 == 1
        } else if d >= N {
            (self.1[d - N] >> b) & 1 == 1
        } else {
            (self.0[d] >> b) & 1 == 1
        }
    }
}

mod tests {
    #[test]
    fn test_mul_buffer_correctness() {
        use super::*;
        type Buf = MulBuffer<10>;
        let temp = Buf::new([10u64; 10], [20u64; 10]);

        for i in 0..20 {
            if i < 10 {
                assert_eq!(temp[i], 10);
            } else {
                assert_eq!(temp[i], 20);
            }
        }
    }

    #[test]
    #[should_panic]
    fn test_mul_buffer_soundness() {
        use super::*;
        type Buf = MulBuffer<10>;
        let temp = Buf::new([10u64; 10], [10u64; 10]);

        for i in 20..21 {
            // indexing `temp[20]` should panic
            assert_eq!(temp[i], 10);
        }
    }
}
