<h1 align="center">ark-ff</h1>
<p align="center">
    <img src="https://github.com/arkworks-rs/algebra/workflows/CI/badge.svg?branch=master">
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
    <a href="https://deps.rs/repo/github/arkworks-rs/algebra"><img src="https://deps.rs/repo/github/arkworks-rs/algebra/status.svg"></a>
</p>

This crate defines Finite Field traits and useful abstraction models that follow these traits.
Implementations of finite fields with concrete parameters can be found in [`arkworks-rs/curves`](https://github.com/arkworks-rs/curves/README.md) under `arkworks-rs/curves/<your favourite curve>/src/fields/`, which are used for some of the popular curves, such as a specific [`Fq`](https://github.com/arkworks-rs/curves/blob/master/bls12_381/src/fields/fq.rs) used in BLS-381.

This crate contains two types of traits:

- `Field` traits: These define interfaces for manipulating field elements, such as addition, multiplication, inverses, square roots, and more.
- Field Parameters: holds the parameters defining the field in question. For extension fields, it also provides additional functionality required for the field, such as operations involving a (cubic or quadratic) non-residue used for constructing the field (`NONRESIDUE`).

The available field traits are:

- [`Field`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/mod.rs#L66) - Interface for the most generic finte field
- [`FftField`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/mod.rs#L275) - Exposes methods that allow for performing efficient FFTs on this field's elements
- [`PrimeField`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/mod.rs#L347) - Field with `p` (`p` prime) elements, later referred to as `Fp`.
- [`SquareRootField`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/mod.rs#L431) - Interface for fields that support square-root operations

The models implemented are:

- [`Quadratic Extension`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/quadratic_extension.rs)
- [`QuadExtField`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/quadratic_extension.rs#L140) - Struct representing a quadratic extension field, in this case holding two elements
- [`QuadExtParameters`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/quadratic_extension.rs#L27) - Trait defining the necessary parameters needed to instantiate a Quadratic Extension Field
- [`Cubic Extension`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/cubic_extension.rs)
- [`CubicExtField`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/cubic_extension.rs#L72) - Struct representing a cubic extension field, holds three elements
- [`CubicExtParameters`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/cubic_extension.rs#L27) - Trait defining the necessary parameters needed to instantiate a Cubic Extension Field
  
The above two models serve as abstractions for constructing the extension fields `Fp^m` directly (i.e. `m` equal 2 or 3) or for creating extension towers to arrive at higher `m`. The latter is done by applying the extensions iteratively, e.g. cubic extension over a quadratic extension field.

- [`Fp2`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/fp2.rs#L103) - Quadratic extension directly on the prime field, i.e. `BaseField == BasePrimeField`
- [`Fp3`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/fp3.rs#L54) - Cubic extension directly on the prime field, i.e. `BaseField == BasePrimeField`
- [`Fp6_2over3`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/fp6_2over3.rs#L48) - Extension tower: quadratic extension on a cubic extension field, i.e. `BaseField = Fp3`, but `BasePrimeField = Fp`.
- [`Fp6_3over2`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/fp6_3over2.rs#L49) - Extension tower, similar to the above except that the towering order is reversed: it's a cubic extension on a quadratic extension field, i.e. `BaseField = Fp2`, but `BasePrimeField = Fp`. Only this latter one is exported by default as `Fp6`.
- [`Fp12_2over3over2`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/fp12_2over3over2.rs#L83) - Extension tower: quadratic extension of the `Fp6_3over2`, i.e. `BaseField = Fp6`.
