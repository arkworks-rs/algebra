## ark-ec

This crate defines several elliptic curve traits, and curve models that follow this traits.
Implementations of particular curves using these curve models can be found in [`arkworks-rs/curves`](https://github.com/arkworks-rs/curves/README.md).

The available elliptic curve traits are
* [`AffineCurve`](https://github.com/arkworks-rs/algebra/blob/master/ec/src/lib.rs#L223) - Interface for elliptic curve points in the 'canonical form' for serialization.
* [`ProjectiveCurve`](https://github.com/arkworks-rs/algebra/blob/master/ec/src/lib.rs#L121) - Interface for elliptic curve points in a representation that is more efficient for most computation.
* [`PairingEngine`](https://github.com/arkworks-rs/algebra/blob/master/ec/src/lib.rs#L44) - Pairing friendly elliptic curves (Contains the pairing function, and acts as a wrapper type on G1, G2, GT, and the relevant fields).
* [`CycleEngine`](https://github.com/arkworks-rs/algebra/blob/master/ec/src/lib.rs#L318) - Wrapper type for a cycle of pairing friendly elliptic curves.

The elliptic curve models implemented are
* [`Short Weierstrass`](https://github.com/arkworks-rs/algebra/blob/master/ec/src/models/short_weierstrass_jacobian.rs) curves. The AffineCurve in this case is the typical short weierstrass point representation, and the ProjectiveCurve is using [Jacobian Coordinates](https://en.wikibooks.org/wiki/Cryptography/Prime_Curve/Jacobian_Coordinates).
* [`Twisted Edwards`](https://github.com/arkworks-rs/algebra/blob/master/ec/src/models/twisted_edwards_extended.rs) curves. The AffineCurve in this case is the standard twisted edwards curve representation, whereas the projective curve is the [Extended Twisted Edwards Coordinates](https://eprint.iacr.org/2008/522.pdf)