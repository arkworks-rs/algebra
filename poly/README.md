## ark-poly

This crate implements traits and implementations for polynomials, smooth cosets of fields, and FFTs for these domains.

### Polynomials

Provides the following traits:

- [`Polynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/mod.rs#L16):
Polynomial trait, ensuring that all implementers have basic arithmetic operations implemented.
(`Add, Sub, Zero`, evaluation at a point, degree, etc.)
- [`UVPolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/mod.rs#L41):
Univariate Polynomial trait.
Essentially it defines ways to serialize to/from a polynomial, given that it is univariate.
- [`MVPolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/mod.rs#L59):
Multivariate Polynomial trait.

There are also three different implementations of polynomials in this crate.

- [`univariate/DensePolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/univariate/dense.rs#L22):
Dense univariate polynomials, where a degree `d` polynomial is represented by `d + 1` coefficients.
Implements [`UVPolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/mod.rs#L41)
- [`univariate/SparsePolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/univariate/sparse.rs#L15): Sparse univariate polynomials.
A polynomial is represented by a list representing all the non-zero terms in the polynomial.
Should only be used when a polynomial is mostly non-zero.
Implements [`Polynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/mod.rs#L16).
- [`multivariate/SparsePolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/multivariate/sparse.rs#L21):
Sparse multivariate polynomials.
The polynomial is represented by its non-zero terms.

A struct [`univariate/DenseOrSparsePolynomial`](https://github.com/arkworks-rs/algebra/blob/master/poly/src/polynomial/univariate/mod.rs#L16) is available,
that allows the user to abstract over the type of univariate polynomial underlying it is.

### Domains

TODO