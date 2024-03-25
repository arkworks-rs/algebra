// The below implementation is a rework of https://github.com/armfazh/h2c-rust-ref
// With some optimisations

use core::marker::PhantomData;

use ark_std::vec::*;

use arrayvec::ArrayVec;
use digest::{ExtendableOutput, FixedOutputReset, Update};

pub trait Expander {
    fn expand(&self, msg: &[u8], length: usize) -> Vec<u8>;
}
const MAX_DST_LENGTH: usize = 255;

const LONG_DST_PREFIX: &[u8; 17] = b"H2C-OVERSIZE-DST-";

/// Implements section [5.3.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16#section-5.3.3)
/// "Using DSTs longer than 255 bytes" of the
/// [IRTF CFRG hash-to-curve draft #16](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16#section-5.3.3).
pub struct DST(arrayvec::ArrayVec<u8, MAX_DST_LENGTH>);

impl DST {
    pub fn new_xmd<H: FixedOutputReset + Default>(dst: &[u8]) -> DST {
        let array = if dst.len() > MAX_DST_LENGTH {
            let mut long = H::default();
            long.update(&LONG_DST_PREFIX[..]);
            long.update(&dst);
            ArrayVec::try_from(long.finalize_fixed().as_ref()).unwrap()
        } else {
            ArrayVec::try_from(dst).unwrap()
        };
        DST(array)
    }

    #[allow(dead_code)]
    pub fn new_xof<H: ExtendableOutput + Default>(dst: &[u8], k: usize) -> DST {
        let array = if dst.len() > MAX_DST_LENGTH {
            let mut long = H::default();
            long.update(&LONG_DST_PREFIX[..]);
            long.update(&dst);

            let mut new_dst = [0u8; MAX_DST_LENGTH];
            let new_dst = &mut new_dst[0..((2 * k + 7) >> 3)];
            long.finalize_xof_into(new_dst);
            ArrayVec::try_from(&*new_dst).unwrap()
        } else {
            ArrayVec::try_from(dst).unwrap()
        };
        DST(array)
    }

    pub fn update<H: Update>(&self, h: &mut H) {
        h.update(self.0.as_ref());
        // I2OSP(len,1) https://www.rfc-editor.org/rfc/rfc8017.txt
        h.update(&[self.0.len() as u8]);
    }
}

#[allow(dead_code)]
pub(super) struct ExpanderXof<H: ExtendableOutput + Clone + Default> {
    pub(super) xofer: PhantomData<H>,
    pub(super) dst: Vec<u8>,
    pub(super) k: usize,
}

impl<H: ExtendableOutput + Clone + Default> Expander for ExpanderXof<H> {
    fn expand(&self, msg: &[u8], n: usize) -> Vec<u8> {
        let mut xofer = H::default();
        xofer.update(msg);

        // I2OSP(len,2) https://www.rfc-editor.org/rfc/rfc8017.txt
        let lib_str = (n as u16).to_be_bytes();
        xofer.update(&lib_str);

        DST::new_xof::<H>(self.dst.as_ref(), self.k).update(&mut xofer);
        xofer.finalize_boxed(n).into_vec()
    }
}

pub(super) struct ExpanderXmd<H: FixedOutputReset + Default + Clone> {
    pub(super) hasher: PhantomData<H>,
    pub(super) dst: Vec<u8>,
    pub(super) block_size: usize,
}

static Z_PAD: [u8; 256] = [0u8; 256];

impl<H: FixedOutputReset + Default + Clone> Expander for ExpanderXmd<H> {
    fn expand(&self, msg: &[u8], n: usize) -> Vec<u8> {
        use digest::typenum::Unsigned;
        // output size of the hash function, e.g. 32 bytes = 256 bits for sha2::Sha256
        let b_len = H::OutputSize::to_usize();
        let ell = (n + (b_len - 1)) / b_len;
        assert!(
            ell <= 255,
            "The ratio of desired output to the output size of hash function is too large!"
        );

        let dst_prime = DST::new_xmd::<H>(self.dst.as_ref());
        // Represent `len_in_bytes` as a 2-byte array.
        // As per I2OSP method outlined in https://tools.ietf.org/pdf/rfc8017.pdf,
        // The program should abort if integer that we're trying to convert is too large.
        assert!(n < (1 << 16), "Length should be smaller than 2^16");
        let lib_str: [u8; 2] = (n as u16).to_be_bytes();

        let mut hasher = H::default();
        hasher.update(&Z_PAD[0..self.block_size]);
        hasher.update(msg);
        hasher.update(&lib_str);
        hasher.update(&[0u8]);
        dst_prime.update(&mut hasher);
        let b0 = hasher.finalize_fixed_reset();

        hasher.update(&b0);
        hasher.update(&[1u8]);
        dst_prime.update(&mut hasher);
        let mut bi = hasher.finalize_fixed_reset();

        let mut uniform_bytes: Vec<u8> = Vec::with_capacity(n);
        uniform_bytes.extend_from_slice(&bi);
        for i in 2..=ell {
            // update the hasher with xor of b_0 and b_i elements
            for (l, r) in b0.iter().zip(bi.iter()) {
                hasher.update(&[*l ^ *r]);
            }
            hasher.update(&[i as u8]);
            dst_prime.update(&mut hasher);
            bi = hasher.finalize_fixed_reset();
            uniform_bytes.extend_from_slice(&bi);
        }
        uniform_bytes.truncate(n);
        uniform_bytes
    }
}

#[cfg(all(test, feature = "std"))]
mod tests;
