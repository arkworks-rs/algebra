# Curve implementations

This directory contains implementations of some popular elliptic curves.

### BLS12-381 and embedded curves
* [`ark-bls12-381`](bls12-381): Implements the BLS12-381 pairing-friendly curve
* [`ark-ed-on-bls12-381`](ed-on-bls12-381): Implements a Twisted Edwards curve atop the scalar field of BLS12-381

### BLS12-377 and related curves
* [`ark-bls12-377`](bls12-377): Implements the BLS12-377 pairing-friendly curve
* [`ark-ed-on-bls12-377`](ed-on-bls12-377): Implements a Twisted Edwards curve atop the scalar field of BLS12-377

* [`ark-bw6-761`](bw6-761): Implements the BW6-761 pairing-friendly curve, which is a curve whose scalar field equals the base field of BLS12-377
* [`ark-ed-on-bw6-761`](ed-on-bw6-761): Implements a Twisted Edwards curve atop the scalar field of BW6-761

* [`ark-cp6-782`](cp6-782): Implements the CP6-782 pairing-friendly curve, which is a curve whose scalar field equals the base field of BLS12-377
* [`ark-ed-on-cp6-782`](ed-on-cp6-782): Implements a Twisted Edwards curve atop the scalar field of CP6-782. This is the same curve as in `ark-ed-on-bw6-761`

### BN254 and related curves
* [`ark-bn254`](bn254): Implements the BN254 pairing-friendly curve
* [`ark-ed-on-bn254`](ed-on-bn254): Implements a Twisted Edwards curve atop the scalar field of BN254

### MNT-298 cycle of curves and related curves
* [`ark-mnt4-298`](mnt4-298): Implements the MNT4-298 pairing-friendly curve. This curve forms a pairing-friendly cycle with MNT6-298
* [`ark-mnt6-298`](mnt6-298): Implements the MNT6-298 pairing-friendly curve. This curve forms a pairing-friendly cycle with MNT4-298
* [`ark-ed-on-mnt4-298`](ed-on-mnt4-298): Implements a Twisted Edwards curve atop the scalar field of MNT4-298

### MNT-753 cycle of curves and related curves
* [`ark-mnt4-753`](mnt4-753): Implements the MNT4-753 pairing-friendly curve. This curve forms a pairing-friendly cycle with MNT6-753
* [`ark-mnt6-753`](mnt6-753): Implements the MNT6-753 pairing-friendly curve. This curve forms a pairing-friendly cycle with MNT4-753
* [`ark-ed-on-mnt4-753`](ed-on-mnt4-753): Implements a Twisted Edwards curve atop the scalar field of MNT4-753