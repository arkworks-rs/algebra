/// Iterates over a slice of `u64` in *big-endian* order.
#[derive(Debug)]
pub struct BitIteratorBE<Slice: AsRef<[u64]>> {
    s: Slice,
    n: usize,
}

impl<Slice: AsRef<[u64]>> BitIteratorBE<Slice> {
    pub fn new(s: Slice) -> Self {
        let n = s.as_ref().len() * 64;
        Self { s, n }
    }

    /// Construct an iterator that automatically skips any leading zeros.
    /// That is, it skips all zeros before the most-significant one.
    pub fn without_leading_zeros(s: Slice) -> impl Iterator<Item = bool> {
        Self::new(s).skip_while(|b| !b)
    }
}

impl<Slice: AsRef<[u64]>> Iterator for BitIteratorBE<Slice> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        if self.n == 0 {
            None
        } else {
            self.n -= 1;
            let part = self.n / 64;
            let bit = self.n - (64 * part);

            Some(self.s.as_ref()[part] & (1 << bit) > 0)
        }
    }
}

/// Iterates over a slice of `u64` in *little-endian* order.
#[derive(Debug)]
pub struct BitIteratorLE<Slice: AsRef<[u64]>> {
    s: Slice,
    n: usize,
    max_len: usize,
}

impl<Slice: AsRef<[u64]>> BitIteratorLE<Slice> {
    pub fn new(s: Slice) -> Self {
        let n = 0;
        let max_len = s.as_ref().len() * 64;
        Self { s, n, max_len }
    }

    /// Construct an iterator that automatically skips any trailing zeros.
    /// That is, it skips all zeros after the most-significant one.
    pub fn without_trailing_zeros(s: Slice) -> impl Iterator<Item = bool> {
        let mut first_trailing_zero = 0;
        for (i, limb) in s.as_ref().iter().enumerate().rev() {
            first_trailing_zero = i * 64 + (64 - limb.leading_zeros()) as usize;
            if *limb != 0 {
                break;
            }
        }
        let mut iter = Self::new(s);
        iter.max_len = first_trailing_zero;
        iter
    }
}

impl<Slice: AsRef<[u64]>> Iterator for BitIteratorLE<Slice> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        if self.n == self.max_len {
            None
        } else {
            let part = self.n / 64;
            let bit = self.n - (64 * part);
            self.n += 1;

            Some(self.s.as_ref()[part] & (1 << bit) > 0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::vec::Vec;

    #[test]
    fn test_bit_iterator_be() {
        // Test with a simple case of a single 64-bit integer: 0b1010
        let data = [0b1010u64];
        let mut iter = BitIteratorBE::new(&data);

        // The iterator should return the bits in big-endian order
        // The first 60 bits are zeros
        for _ in 0..60 {
            assert_eq!(iter.next(), Some(false));
        }
        assert_eq!(iter.next(), Some(true)); // 3rd bit
        assert_eq!(iter.next(), Some(false)); // 2nd bit
        assert_eq!(iter.next(), Some(true)); // 1st bit
        assert_eq!(iter.next(), Some(false)); // 0th bit
        assert_eq!(iter.next(), None); // End of iteration

        // Test with the without_leading_zeros method
        let data = [0b0000_0000_0000_0000_0000_0000_0000_1010u64];
        let iter: Vec<bool> = BitIteratorBE::without_leading_zeros(&data).collect();
        assert_eq!(iter, vec![true, false, true, false]); // Only the significant bits

        // Test with all zeros
        let data = [0u64];
        let iter: Vec<bool> = BitIteratorBE::without_leading_zeros(&data).collect();
        assert!(iter.is_empty()); // Should be empty because all bits are zeros
    }

    #[test]
    fn test_bit_iterator_le() {
        // Test with a simple case of a single 64-bit integer: 0b1010
        let data = [0b1010u64];
        let mut iter = BitIteratorLE::new(&data);

        // The iterator should return the bits in little-endian order
        assert_eq!(iter.next(), Some(false)); // 0th bit
        assert_eq!(iter.next(), Some(true)); // 1st bit
        assert_eq!(iter.next(), Some(false)); // 2nd bit
        assert_eq!(iter.next(), Some(true)); // 3rd bit
        for _ in 4..64 {
            assert_eq!(iter.next(), Some(false)); // The remaining bits are zeros
        }
        assert_eq!(iter.next(), None); // End of iteration

        // Test with the without_trailing_zeros method
        let data = [0b0000_0000_0000_0000_0000_0000_0000_1010u64];
        let iter: Vec<bool> = BitIteratorLE::without_trailing_zeros(&data).collect();
        assert_eq!(iter, vec![false, true, false, true]); // Only the significant bits

        // Test with all zeros
        let data = [0u64];
        let iter: Vec<bool> = BitIteratorLE::without_trailing_zeros(&data).collect();
        assert!(iter.is_empty()); // Should be empty because all bits are zeros
    }

    #[test]
    fn test_bit_iterator_be_multiple_integers() {
        // Test with multiple 64-bit integers: [0b1010, 0b1111]
        let data = [0b1010u64, 0b1111u64];
        let mut iter = BitIteratorBE::new(&data);

        // First integer (0b1111) in big-endian order
        for _ in 0..60 {
            assert_eq!(iter.next(), Some(false));
        }
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));

        // Second integer (0b1010) in big-endian order
        for _ in 0..60 {
            assert_eq!(iter.next(), Some(false));
        }
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), None); // End of iteration
    }

    #[test]
    fn test_bit_iterator_le_multiple_integers() {
        // Test with multiple 64-bit integers: [0b1010, 0b1111]
        let data = [0b1010u64, 0b1111u64];
        let mut iter = BitIteratorLE::new(&data);

        // First integer (0b1010) in little-endian order
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next(), Some(true));
        for _ in 4..64 {
            assert_eq!(iter.next(), Some(false));
        }

        // Second integer (0b1111) in little-endian order
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next(), Some(true));
        for _ in 4..64 {
            assert_eq!(iter.next(), Some(false));
        }
        assert_eq!(iter.next(), None); // End of iteration
    }
}
