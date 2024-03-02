<h1 align="center">ark-ec</h1>
<p align="center">
    <img src="https://github.com/arkworks-rs/algebra/workflows/CI/badge.svg?branch=master">
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
    <a href="https://deps.rs/repo/github/arkworks-rs/algebra"><img src="https://deps.rs/repo/github/arkworks-rs/algebra/status.svg"></a>
</p>

`ark-ec` defines traits and algorithms for working with different kinds of additive groups, with a focus on groups arising from elliptic curves. It further provides concrete instantiations of these traits for various elliptic curve models, including popular families of pairing-friendly curves such as the BLS12 family of curves.
Implementations of particular curves using these curve models can be found in [`arkworks-rs/curves`](https://github.com/arkworks-rs/algebra/blob/master/curves/README.md).

## Usage

### The `Group` trait

Many cryptographic protocols use as core building-blocks prime-order groups. The [`PrimeGroup`](https://github.com/arkworks-rs/algebra/blob/master/ec/src/lib.rs) trait is an abstraction that represents elements of such abelian prime-order groups. It provides methods for performing common operations on group elements:

```rust
use ark_ec::{AdditiveGroup, PrimeGroup};
use ark_ff::{PrimeField, Field};
// We'll use the BLS12-381 G1 curve for this example.
// This group has a prime order `r`, and is associated with a prime field `Fr`.
use ark_test_curves::bls12_381::{G1Projective as G, Fr as ScalarField};
use ark_std::{Zero, UniformRand, ops::Mul};

let mut rng = ark_std::test_rng();
// Let's sample uniformly random group elements:
let a = G::rand(&mut rng);
let b = G::rand(&mut rng);

// We can add elements, ...
let c = a + b;
// ... subtract them, ...
let d = a - b;
// ... and double them.
assert_eq!(c + d, a.double());
// We can also negate elements, ...
let e = -a;
// ... and check that negation satisfies the basic group law
assert_eq!(e + a, G::zero());

// We can also multiply group elements by elements of the corresponding scalar field
// (an act known as *scalar multiplication*)
let scalar = ScalarField::rand(&mut rng);
let e = c.mul(scalar);
let f = e.mul(scalar.inverse().unwrap());
assert_eq!(f, c);
```

## Scalar multiplication

While the `PrimeGroup` trait already produces scalar multiplication routines, in many cases one can take advantage of
the group structure to perform scalar multiplication more efficiently. To allow such specialization, `ark-ec` provides
the `ScalarMul` and `VariableBaseMSM` traits. The latter trait computes an "inner product" between a vector of scalars `s` and a vector of group elements `g`. That is, it computes `s.iter().zip(g).map(|(s, g)| g * s).sum()`.

```rust
use ark_ec::{PrimeGroup, VariableBaseMSM};
use ark_ff::{PrimeField, Field};
// We'll use the BLS12-381 G1 curve for this example.
// This group has a prime order `r`, and is associated with a prime field `Fr`.
use ark_test_curves::bls12_381::{G1Projective as G, G1Affine as GAffine, Fr as ScalarField};
use ark_std::{Zero,  UniformRand};

let mut rng = ark_std::test_rng();
// Let's sample uniformly random group elements:
let a = GAffine::rand(&mut rng);
let b = GAffine::rand(&mut rng);

let s1 = ScalarField::rand(&mut rng);
let s2 = ScalarField::rand(&mut rng);

// Note that we're using the `GAffine` type here, as opposed to `G`.
// This is because MSMs are more efficient when the group elements are in affine form. (See below for why.)
//
// The `VariableBaseMSM` trait allows specializing the input group element representation to allow
// for more efficient implementations.
let r = G::msm(&[a, b], &[s1, s2]).unwrap();
assert_eq!(r, a * s1 + b * s2);
```

### Elliptic curve groups

There are two traits that are important when working with elliptic curves
over finite fields: [`CurveGroup`], and [`AffineRepr`]. Both traits
represent elements of the same curve, but provide different underlying representations.
In particular, the [`CurveGroup`] representation of a curve point is generally
more efficient for arithmetic, but does not provide a unique representative
for a curve point. An [`AffineRepr`] representation, on the other hand, *is* unique,
but is slower for most arithmetic operations. Let's explore how and when to use
these:

```rust
use ark_ec::{AdditiveGroup, AffineRepr, PrimeGroup, CurveGroup, VariableBaseMSM};
use ark_ff::{PrimeField, Field};
use ark_test_curves::bls12_381::{G1Projective as G, G1Affine as GAffine, Fr as ScalarField};
use ark_std::{Zero, UniformRand};

let mut rng = ark_std::test_rng();
// Let's generate an elliptic curve group element in the `CurveGroup` representation
let a = G::rand(&mut rng);
// We can convert it the `AffineRepr` representation...
let a_aff = a.into_affine();
// ... and check that the two representations are equal.
assert_eq!(a_aff, a);
// We can also convert back to the `CurveGroup` representation:
assert_eq!(a, a_aff.into_group());

// As a general rule, most group operations are slower when elements
// are represented as `AffineRepr`. However, adding an `AffineRepr`
// point to a `CurveGroup` one is usually slightly more efficient than
// adding two `CurveGroup` points.
let d = a + a_aff;
assert_eq!(d, a.double());

// This efficiency also translates into more efficient scalar multiplication routines.
let scalar = ScalarField::rand(&mut rng);
let mul_result = a_aff * scalar;
assert_eq!(a * scalar, mul_result);

// Finally, while not recommended, users can directly construct group elements
// from the x and y coordinates of the curve points. This is useful when implementing algorithms
// like hash-to-curve.
let a_x = a_aff.x;
let a_y = a_aff.y;
let is_at_infinity = a_aff.is_zero();
// This check ensures that `new_a` is indeed in the curve group, and in particular
// is within the prime-order group.
let new_a = GAffine::new(a_x, a_y);
assert_eq!(a_aff, new_a);
assert!(new_a.is_on_curve());
assert!(new_a.is_in_correct_subgroup_assuming_on_curve());
```

Besides the foregoing abstract interfaces for elliptic curve groups, `ark-ec` also provides
the following concrete instantiations of common elliptic curve models:

* [*Short Weierstrass*](https://github.com/arkworks-rs/algebra/blob/master/ec/src/models/short_weierstrass.rs) curves. The `AffineRepr` in this case is in typical Short Weierstrass point representation, and the `CurveGroup` is using points in [Jacobian Coordinates](https://en.wikibooks.org/wiki/Cryptography/Prime_Curve/Jacobian_Coordinates).
* [*Twisted Edwards*](https://github.com/arkworks-rs/algebra/blob/master/ec/src/models/twisted_edwards.rs) curves. The `AffineRepr` in this case is in standard Twisted Edwards curve representation, whereas the `CurveGroup` uses points in [Extended Twisted Edwards Coordinates](https://eprint.iacr.org/2008/522.pdf).

### Pairings

[`Pairing`](https://github.com/arkworks-rs/algebra/blob/master/ec/src/pairing.rs) is a trait that defines the interface for a pairing-friendly elliptic curve. Besides the general interface, we provide concrete instantiations of popular pairing-friendly families of curves, such as the [Barreto-Lynn-Scott](https://github.com/arkworks-rs/algebra/blob/master/ec/src/models/bls12/mod.rs) and [Barreto-Naehrig](https://github.com/arkworks-rs/algebra/blob/master/ec/src/models/bn/mod.rs) families.

```rust
use ark_ec::{pairing::Pairing, AffineRepr};
use ark_ff::Field;
use ark_std::UniformRand;

use ark_test_curves::bls12_381::{Bls12_381, G1Projective as G1, G2Projective as G2, Fq12 as Fq12};
use ark_test_curves::bls12_381::Fr as ScalarField;

// The pairing engine is parameterized by the scalar field of the curve.
let mut rng = ark_std::test_rng();
let s = ScalarField::rand(&mut rng);
let a = G1::rand(&mut rng);
let b = G2::rand(&mut rng);

// We can compute the pairing of two points on the curve, either monolithically...
let e1 = Bls12_381::pairing(a, b);
// ... or in two steps. First, we compute the Miller loop...
let ml_result = Bls12_381::miller_loop(a, b);
// ... and then the final exponentiation.
let e2 = Bls12_381::final_exponentiation(ml_result).unwrap();
assert_eq!(e1, e2);
```

### Hash-to-group

`ark-ec` also provides traits for hashing to elliptic curve groups. The [`HashToCurve`](https://github.com/arkworks-rs/algebra/blob/master/ec/src/hashing/mod.rs) trait allows users to hash arbitrary byte strings to elliptic curve group elements, and allows using different hashing strategies.
