## ark-poly

This crate implements traits and implementations for polynomials, FFT-friendly subsets of a field (dubbed "domains"), and FFTs for these domains.

### Polynomials

The `polynomial` module provides the following traits for defining polynomials:

- [`Polynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/mod.rs#L16):
Requires implementors to support common operations on polynomials,
such as `Add`, `Sub`, `Zero`, evaluation at a point, degree, etc,
and defines methods to serialize to and from the coefficient representation of the polynomial.
- [`UVPolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/mod.rs#L41):
Specifies that a `Polynomial` is actually a *univariate* polynomial.
- [`MVPolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/mod.rs#L59):
Specifies that a `Polynomial` is actually a *multivariate* polynomial.

This crate also provides the following data structures that implement these traits:

- [`univariate/DensePolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/univariate/dense.rs#L22):
Represents degree `d` univariate polynomials via a list of `d + 1` coefficients.
This struct implements the [`UVPolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/mod.rs#L41) trait.
- [`univariate/SparsePolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/univariate/sparse.rs#L15):
Represents degree `d` univariate polynomials via a list containing all non-zero monomials.
This should only be used when most coefficients of the polynomial are zero.
This struct implements the [`Polynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/mod.rs#L16) trait
(but *not* the `UVPolynomial` trait).
- [`multivariate/SparsePolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/multivariate/sparse.rs#L21):
Represents multivariate polynomials via a list containing all non-zero monomials.

This crate also provides the [`univariate/DenseOrSparsePolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/univariate/mod.rs#L16) enum, which allows the user to abstract over the type of underlying univariate polynomial (dense or sparse).

### Domains

TODO
