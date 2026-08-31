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

This crate provides abstractions and implementations of FFT-friendly evaluation domains over finite fields.

- `EvaluationDomain<F>`: the core trait that defines the domain API used by FFTs and polynomial operations.
- `GeneralEvaluationDomain<F>`: a wrapper that automatically selects the most efficient domain for the field/size.
- `Radix2EvaluationDomain<F>`: a radix-2 domain for fields with sufficient two-adicity.
- `MixedRadixEvaluationDomain<F>`: a mixed-radix domain for fields exposing an additional small subgroup.

See implementations in `src/domain/` and re-exports from `src/lib.rs`.

### Core concepts

- A domain of size `n` is the multiplicative subgroup (or its coset) generated by a root of unity `g`.
- FFT computes evaluations of a polynomial on the domain; IFFT recovers coefficients from evaluations.
- A coset domain `H = h · <g>` is built by shifting the subgroup with a nonzero `offset = h`.

Key APIs from `EvaluationDomain<F>`:

- `new(num_coeffs) -> Option<Self>` and `compute_size_of_domain(num_coeffs) -> Option<usize>`
- `fft/fft_in_place`, `ifft/ifft_in_place`
- `elements()` and `element(i)` iterators/utilities
- `get_coset(offset)` / `new_coset(size, offset)` and `coset_offset()`
- `vanishing_polynomial()` and `evaluate_vanishing_polynomial(tau)`
- `evaluate_all_lagrange_coefficients(tau)` and `filter_polynomial(subdomain)`

### GeneralEvaluationDomain

`GeneralEvaluationDomain<F>` chooses a `Radix2EvaluationDomain<F>` when possible and falls back to `MixedRadixEvaluationDomain<F>` if the field provides a small additional subgroup. This is the recommended entry point for most users.

```rust
use ark_poly::{GeneralEvaluationDomain, EvaluationDomain};
use ark_poly::{univariate::DensePolynomial};
use ark_test_curves::bls12_381::Fr;

// Create a domain large enough for a polynomial with up to 4 coefficients.
let domain = GeneralEvaluationDomain::<Fr>::new(4).unwrap();

// Start from evaluations, recover the polynomial, then evaluate again.
let evals = vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64), Fr::from(4u64)];
let coeffs = domain.ifft(&evals);
let poly = DensePolynomial::from_coefficients_vec(coeffs.clone());
assert_eq!(poly.degree(), 3);

let roundtrip = domain.fft(&coeffs);
assert_eq!(roundtrip.len(), domain.size());
```

### Radix2EvaluationDomain

`Radix2EvaluationDomain<F>` works for sizes up to `2^F::TWO_ADICITY`. It supports degree-aware FFTs that avoid unnecessary work when the target domain is much larger than the polynomial degree.

```rust
use ark_poly::{Radix2EvaluationDomain, EvaluationDomain};
use ark_test_curves::bls12_381::Fr;

let domain = Radix2EvaluationDomain::<Fr>::new(8).unwrap();
let coset = domain.get_coset(Fr::GENERATOR).unwrap();
assert_eq!(domain.size(), coset.size());

// Iterate over domain elements
for (i, x) in domain.elements().enumerate() {
    assert_eq!(x, domain.group_gen().pow([i as u64]));
}
```

### MixedRadixEvaluationDomain

`MixedRadixEvaluationDomain<F>` targets fields that expose a small subgroup in addition to the 2-adic subgroup; it enables FFT sizes that are products of a power of two and a power of `F::SMALL_SUBGROUP_BASE`.

```rust
use ark_poly::{MixedRadixEvaluationDomain, EvaluationDomain};
use ark_test_curves::bn384_small_two_adicity::Fr; // field with a small extra subgroup

let domain = MixedRadixEvaluationDomain::<Fr>::new(8).unwrap();
assert_eq!(domain.size(), 8);
```

### Vanishing and Lagrange polynomials

You can obtain the vanishing polynomial of a domain and use it for checks, or compute Lagrange basis coefficients at a point for interpolation:

```rust
use ark_poly::{GeneralEvaluationDomain, EvaluationDomain};
use ark_ff::Zero;
use ark_test_curves::bls12_381::Fr;

let d = GeneralEvaluationDomain::<Fr>::new(4).unwrap();
let z = d.vanishing_polynomial();
for x in d.elements() {
    assert!(z.evaluate(&x).is_zero());
}

let tau = Fr::from(7u64);
let lagrange = d.evaluate_all_lagrange_coefficients(tau);
assert_eq!(lagrange.len(), d.size());
```

Notes:

- `GeneralEvaluationDomain::<F>::new(n)` returns `None` if the field `F` is not FFT-friendly for the requested size. In that case, consider adjusting `n` or selecting a different field.
- When the `parallel` feature is enabled, larger transforms may run in parallel.
