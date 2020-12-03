
## Pending

### Breaking changes
- #20 (ark-poly) Move univariate DensePolynomial and SparsePolynomial into a 
    univariate sub-crate. Make this change by:
    find w/ regex `ark_poly::(Dense|Sparse)Polynomial`, and replace with `ark_poly::univariate::$1Polynomial`.
- #36 (ark-ec) In Short-Weierstrass curves, include an infinity bit in `ToConstraintField`.
- #37 (ark-poly) In the `Polynomial` trait, add `Hash` trait bound to `Point`.
- #38 (ark-poly) Add `Add` and `Neg` trait bounds to `Polynomial`.
- #51 (ark-ff) Removed `unitary_inverse` from `QuadExtField`. Make this change by
    replacing `x.unitary_inverse()` with `let mut tmp = x.clone(); tmp.conjugate()`
- #53 (ark-poly) Add `Zero` trait bound to `Polynomial`.
- #106 (ark-ff, ark-ec) Add `Zeroize` trait bound to `Field, ProjectiveGroup, AffineGroup` traits.

### Features
- #20 (ark-poly) Add structs/traits for multivariate polynomials
- #22 (ark-ec) Speedup fixed-base MSMs
- #28 (ark-poly) Add `domain()` method on the `evaluations` struct
- #31 (ark-ec) Speedup point doubling on twisted edwards curves
- #35 (ark-ff) Implement `ToConstraintField` for `bool`
- #48 (ark-ff) Speedup `sqrt` on `QuadExtField`
- #94 (ark-ff) Implement `ToBytes` and `FromBytes` for `u128`
- #99 (ark-poly) Speedup `evaluate_all_lagrange_coefficients`
- #100 (ark-ff) Implement `batch_inverse_and_mul`
- #101 (ark-ff) Add `element(i: usize)` on the `Domain` trait.

### Bug fixes
- #36 (ark-ec) In Short-Weierstrass curves, include an infinity bit in `ToConstraintField`.


## v0.0 (Initial release of arkworks/algebra)
