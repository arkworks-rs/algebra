<h1 align="center">ark-ec</h1>
<p align="center">
    <img src="https://github.com/arkworks-rs/algebra/workflows/CI/badge.svg?branch=master">
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
    <a href="https://deps.rs/repo/github/arkworks-rs/algebra"><img src="https://deps.rs/repo/github/arkworks-rs/algebra/status.svg"></a>
</p>

This crate defines Finite Field traits and useful abstraction models that follow these traits.
Implementations of finite fields with concrete parameters can be found in [`arkworks-rs/curves`](https://github.com/arkworks-rs/curves/README.md) under `arkworks-rs/curves/<your favourite curve>/src/fields/`, which are used for some of the popular curves, such as [`Fq`](https://github.com/arkworks-rs/curves/blob/master/bls12_381/src/fields/fq.rs) used in BLS-381.

It is important to distinguish two types of traits here: 
- Fields: define an interface for basic manipulation of field elements by providing methods for in-place operations (such as doubling or sqrt) and functions inherent to the field. 
- Field Parameters: hold the parameters that define the precise field, as well as provide additional functionality that the field has aquired (e.g. operations involving a QNR by extending the field).


The available traits are:

* [`Field`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/mod.rs#L65) - Interface for the most generic finte field
* [`FftField`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/mod.rs#L273) - Exposes methods that allow for performing FFT on this Field's  elements
* [`PrimeField`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/mod.rs#L345) - Relies on the `Field` supertrait 
* [`SquareRootField`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/mod.rs#L425) - Interface for Fields that support square-root operations, such as ...

The models implemented are:

* [`Quadratic Extension`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/quadratic_extension.rs) - 
* [`Cubic Extension`](https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/cubic_extension.rs) - 
