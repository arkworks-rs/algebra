// The below implementation is a rework of https://github.com/armfazh/h2c-rust-ref
// With some optimisations

use ark_std::vec::Vec;
use crate::{Field};

use digest::{FixedOutputReset, ExtendableOutput, XofReader, Update};
use arrayvec::ArrayVec;


const MAX_DST_LENGTH: usize = 255;

const LONG_DST_PREFIX: &[u8; 17] = b"H2C-OVERSIZE-DST-";

/// Implements section [5.3.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16#section-5.3.3)
/// "Using DSTs longer than 255 bytes" of the 
/// [IRTF CFRG hash-to-curve draft #16](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-16#section-5.3.3).
pub struct DST(arrayvec::ArrayVec<u8,MAX_DST_LENGTH>);

impl TryFrom<&'static [u8]> for DST {
    type Error = &'static str;
    fn try_from(dst: &'static [u8]) -> Result<Self, Self::Error> {
        Ok(DST(ArrayVec::try_from(dst).map_err(|_| "DST longer than 255 bytes!") ?))
    }
}

/*
impl From<&'static [u8]> for DST {
    fn from(dst: &'static [u8]) -> Self {
        ArrayVec::try_from(dst).expect("DST longer than 255 bytes!");
    }
}
*/

impl DST {
    pub fn new_xmd<H: FixedOutputReset+Default>(dst: &[u8]) -> DST {
        DST(ArrayVec::try_from(dst).unwrap_or_else( |_| {
            let mut long = H::default();
            long.update(&LONG_DST_PREFIX[..]);
            long.update(&dst);
            ArrayVec::try_from( long.finalize_fixed().as_ref() ).unwrap()
        } ))
    }

    // pub fn sec_param<H: 'static>(dst: &[u8]) -> usize {
    //     use core::any::TypeId;
    //     match TypeId::of::<H> {
    //         TypeId::of::<sha3::Shake128> => 128,
    //         TypeId::of::<sha3::Shake256> => 256,
    //     }
    // }

    pub fn new_xof<H: ExtendableOutput+Default>(dst: &[u8], sec_param: Option<u16>) -> DST {
        DST(ArrayVec::try_from(dst).unwrap_or_else( |_| {
            let sec_param = sec_param.expect("expand_message_xof wants a security parameter for compressing a long domain string.") as usize;
            let mut long = H::default();
            long.update(&LONG_DST_PREFIX[..]);
            long.update(&dst);

            let mut new_dst = [0u8; MAX_DST_LENGTH];
            let new_dst = &mut new_dst[0..((2 * sec_param + 7) >> 3)];
            long.finalize_xof_into(new_dst);
            ArrayVec::try_from( &*new_dst ).unwrap()
        } ))
    }

    pub fn update<H: Update>(&self, h: &mut H) {
        h.update(self.0.as_ref());
        // I2OSP(len,1) https://www.rfc-editor.org/rfc/rfc8017.txt
        h.update(&[self.0.len() as u8]);
    }
}

pub trait Expander: Sized {
    type R: XofReader;
    fn expand(self, dst: &DST, length: usize) -> Self::R;
    fn expand_for_field<const SEC_PARAM: u16,F: Field,const N: usize>(self, dst: &DST) -> Self::R {
        let len_per_base_elem = super::get_len_per_elem::<F, SEC_PARAM>();
        let m = F::extension_degree() as usize;
        let total_length = N * m * len_per_base_elem;
        self.expand(&dst, total_length)
    }
}

impl<H: ExtendableOutput> Expander for H {
    type R = <H as ExtendableOutput>::Reader;
    fn expand(mut self, dst: &DST, n: usize) -> Self::R
    {
        assert!(n < (1 << 16), "Length should be smaller than 2^16");
        // I2OSP(len,2) https://www.rfc-editor.org/rfc/rfc8017.txt
        self.update(& (n as u16).to_be_bytes());
    
        dst.update(&mut self);
        self.finalize_xof()
    }
}

static Z_PAD: [u8; 256] = [0u8; 256];

pub struct Zpad<H: FixedOutputReset+Default>(pub H);

impl<H: FixedOutputReset+Default> Update for Zpad<H> {
    fn update(&mut self, data: &[u8]) {
        self.0.update(data);
    }
}

impl<H: FixedOutputReset+Default> Zpad<H> {
    pub fn new(block_size: usize) -> Zpad<H> {
        let mut hasher = H::default();
        hasher.update(&Z_PAD[0..block_size]);
        Zpad(hasher)
    }
    pub fn new_for_field<const SEC_PARAM: u16,F: Field>() -> Zpad<H> {
        let len_per_base_elem = super::get_len_per_elem::<F, SEC_PARAM>();
        Self::new(len_per_base_elem)
    }
}

impl<H: FixedOutputReset+Default> Expander for Zpad<H> {
    type R = XofVec;
    fn expand(self, dst: &DST, n: usize) -> XofVec
    {
        use digest::typenum::Unsigned;
        // output size of the hash function, e.g. 32 bytes = 256 bits for sha2::Sha256
        let b_len = H::OutputSize::to_usize();
        let ell = (n + (b_len - 1)) / b_len;
        assert!(
            ell <= 255,
            "The ratio of desired output to the output size of hash function is too large!"
        );

        let Zpad(mut hasher) = self;
        assert!(n < (1 << 16), "Length should be smaller than 2^16");
        // I2OSP(len,2) https://www.rfc-editor.org/rfc/rfc8017.txt
        hasher.update(& (n as u16).to_be_bytes());

        hasher.update(&[0u8]);
        dst.update(& mut hasher);
        let b0 = hasher.finalize_fixed_reset();

        hasher.update(&b0);
        hasher.update(&[1u8]);
        dst.update(& mut hasher);
        let mut bi = hasher.finalize_fixed_reset();

        let mut bytes: Vec<u8> = Vec::with_capacity(n); 
        bytes.extend_from_slice(&bi);
        for i in 2..=ell {
            // update the hasher with xor of b_0 and b_i elements
            for (l, r) in b0.iter().zip(bi.iter()) {
                hasher.update(&[*l ^ *r]);
            }
            hasher.update(&[i as u8]);
            dst.update(& mut hasher);
            bi = hasher.finalize_fixed_reset();
            bytes.extend_from_slice(&bi);
        }
        bytes.truncate(n);
        XofVec { bytes, pos: 0 }
    }
}

pub struct XofVec {
    bytes: Vec<u8>,
    pos: usize,
}

impl XofReader for XofVec {
    fn read(&mut self, buffer: &mut [u8]) {
        let end = self.pos + buffer.len();
        if end > self.bytes.len() {
            panic!("Read more than claimed form expand_message_xmd")
        }
        buffer.copy_from_slice(&self.bytes[self.pos..end]);
        self.pos = end;
    }
}


#[cfg(all(test, feature = "std"))]
mod tests;
