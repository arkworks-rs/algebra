# Curve implementations

This repository contains implementations of some popular elliptic curves. The curve API implemented here matches the curve traits defined in [ark-ec](https://github.com/arkworks-rs/algebra/blob/master/ec/src/lib.rs).

### BLS12-381 and embedded curves

* [`ark-bls12-381`](bls12_381): Implements the BLS12-381 pairing-friendly curve
* [`ark-ed-on-bls12-381`](ed_on_bls12_381): Implements a Twisted Edwards curve atop the scalar field of BLS12-381
* [`ark-ed-on-bls12-381-bandersnatch`](ed_on_bls12_381_bandersnatch): Implements Bandersnatch, another Twisted Edwards curve atop the scalar field of BLS12-381

### BLS12-377 and related curves

* [`ark-bls12-377`](bls12_377): Implements the BLS12-377 pairing-friendly curve
* [`ark-ed-on-bls12-377`](ed_on_bls12_377): Implements a Twisted Edwards curve atop the scalar field of BLS12-377

* [`ark-bw6-761`](bw6_761): Implements the BW6-761 pairing-friendly curve, which is a curve whose scalar field equals the base field of BLS12-377
* [`ark-ed-on-bw6-761`](ed_on_bw6_761): Implements a Twisted Edwards curve atop the scalar field of BW6-761

* [`ark-cp6-782`](cp6_782): Implements the CP6-782 pairing-friendly curve, which is a curve whose scalar field equals the base field of BLS12-377
* [`ark-ed-on-cp6-782`](ed_on_cp6_782): Implements a Twisted Edwards curve atop the scalar field of CP6-782. This is the same curve as in `ark-ed-on-bw6-761`

### BN254 and related curves

* [`ark-bn254`](bn254): Implements the BN254 pairing-friendly curve
* [`ark-ed-on-bn254`](ed_on_bn254): Implements a Twisted Edwards curve atop the scalar field of BN254
* [`ark-babyjubjub`](baby_jubjub): Implements Baby Jubjub, the [ERC-2494](https://eips.ethereum.org/EIPS/eip-2494)-standardized Twisted Edwards curve atop the scalar field of BN254
* [`ark-grumpkin`](grumpkin): Implements the Grumpkin curve. A curve that forms a cycle with bn254.

`ark-ed-on-bn254` and `ark-babyjubjub` are two representations of the *same* Twisted Edwards curve over the scalar field of BN254, related by an isomorphism (a rescaling of the `x` coordinate). They differ in their curve parameters and generator, and are therefore **not** interchangeable at the byte/coordinate level:
* `ark-ed-on-bn254` uses the arkworks-canonical normalized form with `a = 1` (and `d = 168696/168700 mod q`), which is slightly more efficient for in-arkworks arithmetic, together with an arkworks-specific generator.
* `ark-babyjubjub` uses the exact ERC-2494 parameters (`A = 168700`, `D = 168696`) and the standard base point defined in that spec. Prefer this crate when you need coordinates, serialized points, or test vectors that are compatible with the wider Baby Jubjub ecosystem (e.g. circomlib / iden3).

### MNT-298 cycle of curves and related curves

* [`ark-mnt4-298`](mnt4_298): Implements the MNT4-298 pairing-friendly curve. This curve forms a pairing-friendly cycle with MNT6-298
* [`ark-mnt6-298`](mnt6_298): Implements the MNT6-298 pairing-friendly curve. This curve forms a pairing-friendly cycle with MNT4-298
* [`ark-ed-on-mnt4-298`](ed_on_mnt4_298): Implements a Twisted Edwards curve atop the scalar field of MNT4-298

### MNT-753 cycle of curves and related curves

* [`ark-mnt4-753`](mnt4_753): Implements the MNT4-753 pairing-friendly curve. This curve forms a pairing-friendly cycle with MNT6-753
* [`ark-mnt6-753`](mnt6_753): Implements the MNT6-753 pairing-friendly curve. This curve forms a pairing-friendly cycle with MNT4-753
* [`ark-ed-on-mnt4-753`](ed_on_mnt4_753): Implements a Twisted Edwards curve atop the scalar field of MNT4-753

### [Pasta](https://electriccoin.co/blog/the-pasta-curves-for-halo-2-and-beyond/) cycle of curves

* [`ark-pallas`](pallas): Implements Pallas, a prime-order curve that forms an amicable pair with Vesta
* [`ark-vesta`](vesta): Implements Vesta, a prime-order curve that forms an amicable pair with Pallas
