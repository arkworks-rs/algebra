extern crate ark_bls12_381;

use ark_bls12_381::G1Projective as GroupProjective;
use ark_ff::{
    BigInteger384 as BaseFieldBigInt,
    BigInteger512 as FrWideBigInt,
};
use glv_lattice_basis::*;

fn main() {
    print_glv_params::<GroupProjective, FrWideBigInt, BaseFieldBigInt>();
}
