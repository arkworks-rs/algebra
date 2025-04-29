<h1 align="center">ark-poly</h1>
<p align="center">
    <img src="https://github.com/arkworks-rs/algebra/workflows/CI/badge.svg?branch=master">
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
    <a href="https://deps.rs/repo/github/arkworks-rs/algebra"><img src="https://deps.rs/repo/github/arkworks-rs/algebra/status.svg"></a>
</p>

This crate implements traits and implementations for polynomials, FFT-friendly subsets of a field (dubbed "domains"), and FFTs for these domains.

## Polynomials

The `polynomial` module provides the following traits for defining polynomials in coefficient form:

- [`Polynomial`](./src/polynomial/mod.rs#L16):
Requires implementors to support common operations on polynomials,
such as `Add`, `Sub`, `Zero`, evaluation at a point, degree, etc,
and defines methods to serialize to and from the coefficient representation of the polynomial.
- [`DenseUVPolynomial`](./src/polynomial/mod.rs#L43) :
Specifies that a `Polynomial` is actually a *univariate* polynomial.
- [`DenseMVPolynomial`](./src/polynomial/mod.rs#L59):
Specifies that a `Polynomial` is actually a *multivariate* polynomial.

This crate also provides the following data structures that implement these traits:

- [`univariate/DensePolynomial`](./src/polynomial/univariate/dense.rs#L22):
Represents degree `d` univariate polynomials via a list of `d + 1` coefficients.
This struct implements the [`DenseUVPolynomial`](./src/polynomial/mod.rs#L43) trait.
- [`univariate/SparsePolynomial`](./src/polynomial/univariate/sparse.rs#L15):
Represents degree `d` univariate polynomials via a list containing all non-zero monomials.
This should only be used when most coefficients of the polynomial are zero.
This struct implements the [`Polynomial`](./src/polynomial/mod.rs#L16) trait
(but *not* the `DenseUVPolynomial` trait).
- [`multivariate/SparsePolynomial`](./src/polynomial/multivariate/sparse.rs#L21):
Represents multivariate polynomials via a list containing all non-zero monomials.

This crate also provides the [`univariate/DenseOrSparsePolynomial`](./src/polynomial/univariate/mod.rs#L16) enum, which allows the user to abstract over the type of underlying univariate polynomial (dense or sparse).

### Example

```rust
use ark_poly::{
    polynomial::multivariate::{SparsePolynomial, SparseTerm, Term},
    DenseMVPolynomial, Polynomial,
};
use ark_test_curves::bls12_381::Fq;
// Create a multivariate polynomial in 3 variables, with 4 terms:
// f(x_0, x_1, x_2) = 2*x_0^3 + x_0*x_2 + x_1*x_2 + 5
let poly = SparsePolynomial::from_coefficients_vec(
    3,
    vec![
        (Fq::from(2), SparseTerm::new(vec![(0, 3)])),
        (Fq::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
        (Fq::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
        (Fq::from(5), SparseTerm::new(vec![])),
    ],
);
assert_eq!(poly.evaluate(&vec![Fq::from(2), Fq::from(3), Fq::from(6)]), Fq::from(51));
```

## Evaluations

The `evaluations` module provides data structures to represent univariate polynomials in lagrange form.

- [`univariate/Evaluations`](./src/evaluations/univariate/mod.rs#L18)
Represents a univariate polynomial in evaluation form, which can be used for FFT.

The `evaluations` module also provides the following traits for defining multivariate polynomials in lagrange form:

- [`multivariate/multilinear/MultilinearExtension`](./src/evaluations/multivariate/multilinear/mod.rs#L23)
Specifies a multilinear polynomial evaluated over boolean hypercube.
  
This crate provides some data structures to implement these traits.

- [`multivariate/multilinear/DenseMultilinearExtension`](./src/evaluations/multivariate/multilinear/dense.rs#L17)
Represents multilinear extension via a list of evaluations over boolean hypercube.
  
- [`multivariate/multilinear/SparseMultilinearExtension`](./src/evaluations/multivariate/multilinear/sparse.rs#L20)
Represents multilinear extension via a list of non-zero evaluations over boolean hypercube.

### Example

```rust
use ark_test_curves::bls12_381::Fq;
use ark_poly::{DenseMultilinearExtension, MultilinearExtension, SparseMultilinearExtension};
use ark_poly::{
    polynomial::multivariate::{SparsePolynomial, SparseTerm, Term},
    DenseMVPolynomial, Polynomial,
};
use ark_std::One;

// Create a multivariate polynomial in 3 variables:
// f(x_0, x_1, x_2) = 2*x_0^3 + x_0*x_2 + x_1*x_2 
let f = SparsePolynomial::from_coefficients_vec(
    3,
    vec![
        (Fq::from(2), SparseTerm::new(vec![(0, 3)])),
        (Fq::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
        (Fq::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
        (Fq::from(0), SparseTerm::new(vec![])),
    ],
);
// g is the multilinear extension of f, defined by the evaluations of f on the Boolean hypercube:
// f(0, 0, 0) = 2*0^3 + 0*0 + 0*0 = 0
// f(1, 0, 0) = 2*1^3 + 0*0 + 0*0 = 2
// ...
// f(1, 1, 1) = 2*1^3 + 1*1 + 1*1 = 4
let g: DenseMultilinearExtension<Fq> = DenseMultilinearExtension::from_evaluations_vec(
    3, 
    vec![
        Fq::from(0),
        Fq::from(2),
        Fq::from(0),
        Fq::from(2),
        Fq::from(0),
        Fq::from(3),
        Fq::from(1),
        Fq::from(4),
    ]
);
// when evaluated at any point within the Boolean hypercube, f and g should be equal
let point_within_hypercube = &vec![Fq::from(0), Fq::from(1), Fq::from(1)];
assert_eq!(f.evaluate(&point_within_hypercube), g.evaluate(&point_within_hypercube));

// We can also define a MLE g'(x_0, x_1, x_2) by providing the list of non-zero evaluations:
let g_prime: SparseMultilinearExtension<Fq> = SparseMultilinearExtension::from_evaluations(
    3,
    &vec![
        (1, Fq::from(2)),
        (3, Fq::from(2)),
        (5, Fq::from(3)),
        (6, Fq::from(1)),
        (7, Fq::from(4)),
    ]
);
// at any random point (X0, X1, X2), g == g' with negligible probability, unless they are the same function
let random_point = &vec![Fq::from(123), Fq::from(456), Fq::from(789)];
assert_eq!(g_prime.evaluate(&random_point), g.evaluate(&random_point));

```

## Domains

This crate provides implementations of domains over which finite field (I)FFTs can be performed. These domains are essential for efficient polynomial operations, such as interpolation and evaluation.

The `domain` module provides the following trait for defining evaluation domains:

- [`EvaluationDomain`](./src/domain/mod.rs#L27):
Requires implementors to support common operations on domains, such as FFT, iFFT, element access, vanishing polynomial evaluation, etc.

The crate also provides the following concrete domain implementations:

- [`GeneralEvaluationDomain`](./src/domain/general.rs#L39):
A wrapper around specific domain implementations that automatically chooses the most efficient implementation depending on the number of coefficients and the characteristics of the field. This is the recommended domain to use for most applications.

- [`Radix2EvaluationDomain`](./src/domain/radix2/mod.rs#L16):
Represents domains of size 2^n, efficient for fields with high 2-adicity. Supports FFTs of size at most 2^F::TWO_ADICITY.

- [`MixedRadixEvaluationDomain`](./src/domain/mixed_radix.rs#L25):
Suitable for fields that don't have a high enough two-adicity for efficient FFT. Combines the multiplicative subgroup generated by the 2-adic root of unity with another subgroup to form a larger domain.

### Example

```rust
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial};
use ark_test_curves::bls12_381::Fr;

// Create a domain that can fit a polynomial with up to 1024 coefficients
let domain = GeneralEvaluationDomain::<Fr>::new(1024).unwrap();

// Create a polynomial with coefficients [1, 2, 3, 4]
let poly = DensePolynomial::from_coefficients_vec(vec![Fr::from(1), Fr::from(2), Fr::from(3), Fr::from(4)]);

// Evaluate the polynomial at all points in the domain using FFT
let evaluations = domain.fft(&poly.coeffs);

// Interpolate the polynomial from the evaluations using iFFT
let coefficients = domain.ifft(&evaluations);
assert_eq!(coefficients[0..4], poly.coeffs[..]);

// Create a coset domain with an offset
let offset = Fr::from(7);
let coset_domain = domain.get_coset(offset).unwrap();

// Vanishing polynomial evaluation
let point = Fr::from(5);
let vanishing_value = domain.evaluate_vanishing_polynomial(point);
```
