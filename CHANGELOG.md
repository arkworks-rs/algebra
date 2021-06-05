# CHANGELOG

## Pending

### Breaking changes

### Features

### Improvements

### Bug fixes

## v0.3.0

### Breaking changes

- [\#285](https://github.com/arkworks-rs/algebra/pull/285) (ark-ec) Remove `ATE_LOOP_COUNT_IS_NEGATIVE` from BN curve parameter trait.
- [\#292](https://github.com/arkworks-rs/algebra/pull/292) (ark-ec) Remove `CycleEngine`.
- [\#293](https://github.com/arkworks-rs/algebra/pull/293) (ark-ff) Remove `ark_ff::test_rng`.

### Features

- [\#230](https://github.com/arkworks-rs/algebra/pull/230) (ark-ec) Add `wnaf_mul` implementation for `ProjectiveCurve`.
- [\#245](https://github.com/arkworks-rs/algebra/pull/245) (ark-poly) Speedup the sequential and parallel radix-2 FFT and IFFT significantly by making the method in which it accesses roots more cache-friendly.
- [\#258](https://github.com/arkworks-rs/algebra/pull/258) (ark-poly) Add `Mul<F>` implementation for `DensePolynomial`.
- [\#259](https://github.com/arkworks-rs/algebra/pull/259) (ark-poly) Add `Mul<F>` implementation for `SparsePolynomial` and `Add<SparsePolynomial<F>>/Sub<SparsePolynomial<F>>` for `DensePolynomial`.
- [\#261](https://github.com/arkworks-rs/algebra/pull/261) (ark-ff) Add support for 448-bit integers and fields.
- [\#263](https://github.com/arkworks-rs/algebra/pull/263) (ark-ff) Add `From<iXXX>` implementations to fields.
- [\#265](https://github.com/arkworks-rs/algebra/pull/265) (ark-serialize) Add hashing as an extension trait of `CanonicalSerialize`.
- [\#280](https://github.com/arkworks-rs/algebra/pull/280) (ark-ff) Add `Into<BigUint>` and `From<BigUint>` implementations to `BigInteger` and `PrimeField`.
- [\#289](https://github.com/arkworks-rs/algebra/pull/289) (ark-ec) Add `Sum` implementation for all `AffineCurve`.

### Improvements

- [\#279](https://github.com/arkworks-rs/algebra/pull/279) (ark-ec) Parallelize miller loop operations for BLS12.

### Bug fixes

- [\#252](https://github.com/arkworks-rs/algebra/pull/252) (ark-ff) Fix prime field sampling when `REPR_SHIFT_BITS` is 64.
- [\#284](https://github.com/arkworks-rs/algebra/pull/284) (ark-poly-benches) Fix the panic `subgroup_fft_in_place` benchmark for MNT6-753's Fr.

## v0.2.0

The main features of this release are:

- Adding the ability to define fields with integer parameters
- Multi-variate polynomial support
- Multilinear polynomial support
- Many speedups to operations involving polynomials
- Some speedups to `sqrt`
- Small speedups to MSMs
- Big speedups to radix-2 FFTs
- Fix in the assembly arithmetic backend
- Adding new traits for basic curve cycles and pairing based curve cycles

### Breaking changes

- [\#20](https://github.com/arkworks-rs/algebra/pull/20) (ark-poly) Move univariate DensePolynomial and SparsePolynomial into a
    univariate sub-crate. Make this change by:
    find w/ regex `ark_poly::(Dense|Sparse)Polynomial`, and replace with `ark_poly::univariate::$1Polynomial`.
- [\#36](https://github.com/arkworks-rs/algebra/pull/36) (ark-ec) In Short-Weierstrass curves, include an infinity bit in `ToConstraintField`.
- [\#37](https://github.com/arkworks-rs/algebra/pull/37) (ark-poly) In the `Polynomial` trait, add `Hash` trait bound to `Point`.
- [\#38](https://github.com/arkworks-rs/algebra/pull/38) (ark-poly) Add `Add` and `Neg` trait bounds to `Polynomial`.
- [\#51](https://github.com/arkworks-rs/algebra/pull/51) (ark-ff) Removed `unitary_inverse` from `QuadExtField`. Make this change by
    replacing `x.unitary_inverse()` with `let mut tmp = x.clone(); tmp.conjugate()`.
- [\#53](https://github.com/arkworks-rs/algebra/pull/53) (ark-poly) Add `Zero` trait bound to `Polynomial`.
- [\#96](https://github.com/arkworks-rs/algebra/pull/96) (ark-ff) Make the `field_new` macro accept values in integer form, without requiring decomposition into limbs, and without requiring encoding in Montgomery form.
- [\#106](https://github.com/arkworks-rs/algebra/pull/106) (ark-ff, ark-ec) Add `Zeroize` trait bound to `Field, ProjectiveGroup, AffineGroup` traits.
- [\#108](https://github.com/arkworks-rs/algebra/pull/108) (ark-ff) Add `extension_degree()` method to `Field`.
- [\#110](https://github.com/arkworks-rs/algebra/pull/110) (ark-ec) Change the trait bound on the scalar for `mul`, from (essentially) `Into<BigInt>` to `AsRef<[u64]>`.
- [\#117](https://github.com/arkworks-rs/algebra/pull/117) (ark-poly) Make the univariate `SparsePolynomial` implement `Polynomial`. Make this change
    by replacing `sparse_poly.evaluate(pt)` to `sparse_poly.evaluate(&pt)`.
- [\#129](https://github.com/arkworks-rs/algebra/pull/129) (ark-ff) Move `ark_ff::{UniformRand, test_rng}` to `ark_std::{UniformRand, test_rng}`.
    Importing these from `ark-ff` is still possible, but is deprecated and will be removed in the following release.
- [\#144](https://github.com/arkworks-rs/algebra/pull/144) (ark-poly) Add `CanonicalSerialize` and `CanonicalDeserialize` trait bounds for `Polynomial`.
- [\#160](https://github.com/arkworks-rs/algebra/pull/160) (ark-serialize, ark-ff, ark-ec)
    - Remove `ConstantSerializedSize`; users should use `serialized_size*` (see next).
    - Add `serialized_size_with_flags` method to `CanonicalSerializeWithFlags`.
    - Change `from_random_bytes_with_flags` to output `ark_serialize::Flags`.
    - Change signatures of `Flags::from_u8*` to output `Option`.
    - Change `Flags::from_u8*` to be more strict about the inputs they accept:
      if the top bits of the `u8` value do *not* correspond to one of the possible outputs of `Flags::u8_bitmask`, then these methods output `None`, whereas before they output
      a default value.
    Downstream users other than `ark-curves` should not see breakage unless they rely on these methods/traits explicitly.
- [\#165](https://github.com/arkworks-rs/algebra/pull/165) (ark-ff) Add `from_base_field_elements` as a method to the `Field` trait.
- [\#166](https://github.com/arkworks-rs/algebra/pull/166) (ark-ff) Change `BigInt::{from_bytes, to_bits}` to `from_bytes_le, from_bytes_be, to_bits_le, to_bits_be`.

### Features

- [\#20](https://github.com/arkworks-rs/algebra/pull/20) (ark-poly) Add structs/traits for multivariate polynomials.
- [\#96](https://github.com/arkworks-rs/algebra/pull/96) (ark-ff) Make the `field_new` macro accept values in integer form, without requiring decomposition into limbs, and without requiring encoding in Montgomery form.
- [\#106](https://github.com/arkworks-rs/algebra/pull/106) (ark-ff, ark-ec) Add `Zeroize` trait bound to `Field, ProjectiveGroup, AffineGroup` traits.
- [\#117](https://github.com/arkworks-rs/algebra/pull/117) (ark-poly) Add operations to `SparsePolynomial`, so it implements `Polynomial`.
- [\#140](https://github.com/arkworks-rs/algebra/pull/140) (ark-poly) Add support for multilinear extensions in dense and sparse evaluation form.
- [\#164](https://github.com/arkworks-rs/algebra/pull/164) (ark-ff) Add methods `from_{be, le}_bytes_mod_order` to the `PrimeField` trait.
- [\#197](https://github.com/arkworks-rs/algebra/pull/197) (ark-test-curves) Add a BN384 curve with low two-arity for mixed-radix testing.

### Improvements

- [\#22](https://github.com/arkworks-rs/algebra/pull/22) (ark-ec) Speedup fixed-base MSMs.
- [\#28](https://github.com/arkworks-rs/algebra/pull/28) (ark-poly) Add `domain()` method on the `evaluations` struct.
- [\#31](https://github.com/arkworks-rs/algebra/pull/31) (ark-ec) Speedup point doubling on twisted edwards curves.
- [\#35](https://github.com/arkworks-rs/algebra/pull/35) (ark-ff) Implement `ToConstraintField` for `bool`.
- [\#48](https://github.com/arkworks-rs/algebra/pull/48) (ark-ff) Speedup `sqrt` on `QuadExtField`.
- [\#94](https://github.com/arkworks-rs/algebra/pull/94) (ark-ff) Implement `ToBytes` and `FromBytes` for `u128`.
- [\#99](https://github.com/arkworks-rs/algebra/pull/99) (ark-poly) Speedup `evaluate_all_lagrange_coefficients`.
- [\#100](https://github.com/arkworks-rs/algebra/pull/100) (ark-ff) Implement `batch_inverse_and_mul`.
- [\#101](https://github.com/arkworks-rs/algebra/pull/101) (ark-ff) Add `element(i: usize)` on the `Domain` trait.
- [\#107](https://github.com/arkworks-rs/algebra/pull/107) (ark-serialize) Add an impl of `CanonicalSerialize/Deserialize` for `BTreeSet`.
- [\#114](https://github.com/arkworks-rs/algebra/pull/114) (ark-poly) Significantly speedup and reduce memory usage of `DensePolynomial.evaluate`.
- [\#114](https://github.com/arkworks-rs/algebra/pull/114), #119 (ark-poly) Add infrastructure for benchmarking `DensePolynomial` operations.
- [\#115](https://github.com/arkworks-rs/algebra/pull/115) (ark-poly) Add parallel implementation to operations on `Evaluations`.
- [\#115](https://github.com/arkworks-rs/algebra/pull/115) (ark-ff) Add parallel implementation of `batch_inversion`.
- [\#122](https://github.com/arkworks-rs/algebra/pull/122) (ark-poly) Add infrastructure for benchmarking `FFT`s.
- [\#125](https://github.com/arkworks-rs/algebra/pull/125) (ark-poly) Add parallelization to applying coset shifts within `coset_fft`.
- [\#126](https://github.com/arkworks-rs/algebra/pull/126) (ark-ec) Use `ark_ff::batch_inversion` for point normalization.
- [\#131](https://github.com/arkworks-rs/algebra/pull/131), #137 (ark-ff) Speedup `sqrt` on fields when a square root exists. (And slows it down when doesn't exist.)
- [\#141](https://github.com/arkworks-rs/algebra/pull/141) (ark-ff) Add `Fp64`.
- [\#144](https://github.com/arkworks-rs/algebra/pull/144) (ark-poly) Add serialization for polynomials and evaluations.
- [\#149](https://github.com/arkworks-rs/algebra/pull/149) (ark-serialize) Add an impl of `CanonicalSerialize/Deserialize` for `String`.
- [\#153](https://github.com/arkworks-rs/algebra/pull/153) (ark-serialize) Add an impl of `CanonicalSerialize/Deserialize` for `Rc<T>`.
- [\#157](https://github.com/arkworks-rs/algebra/pull/157) (ark-ec) Speed up `variable_base_msm` by not relying on unnecessary normalization.
- [\#158](https://github.com/arkworks-rs/algebra/pull/158) (ark-serialize) Add an impl of `CanonicalSerialize/Deserialize` for `()`.
- [\#166](https://github.com/arkworks-rs/algebra/pull/166) (ark-ff) Add a `to_bytes_be()` and `to_bytes_le` methods to `BigInt`.
- [\#169](https://github.com/arkworks-rs/algebra/pull/169) (ark-poly) Improve radix-2 FFTs by moving to a faster algorithm by Riad S. Wahby.
- [\#171](https://github.com/arkworks-rs/algebra/pull/171), #173, #176 (ark-poly) Apply significant further speedups to the new radix-2 FFT.
- [\#188](https://github.com/arkworks-rs/algebra/pull/188) (ark-ec) Make Short Weierstrass random sampling result in an element with unknown discrete log.
- [\#190](https://github.com/arkworks-rs/algebra/pull/190) (ark-ec) Add curve cycle trait and extended pairing cycle trait for all types of ec cycles.
- [\#201](https://github.com/arkworks-rs/algebra/pull/201) (ark-ec, ark-ff, ark-test-curves, ark-test-templates) Remove the dependency on `rand_xorshift`.
- [\#205](https://github.com/arkworks-rs/algebra/pull/205) (ark-ec, ark-ff) Unroll loops and conditionally use intrinsics in `biginteger` arithmetic, and reduce copies in `ff` and `ec` arithmetic.
- [\#207](https://github.com/arkworks-rs/algebra/pull/207) (ark-ff) Improve performance of extension fields when the non-residue is negative. (Improves fq2, fq12, and g2 speed on bls12 and bn curves.)
- [\#211](https://github.com/arkworks-rs/algebra/pull/211) (ark-ec) Improve performance of BLS12 final exponentiation.
- [\#214](https://github.com/arkworks-rs/algebra/pull/214) (ark-poly) Utilise a more efficient way of evaluating a polynomial at a single point.
- [\#242](https://github.com/arkworks-rs/algebra/pull/242), [\#244][https://github.com/arkworks-rs/algebra/pull/244] (ark-poly) Speedup the sequential radix-2 FFT significantly by making the method in which it accesses roots more cache-friendly.

### Bug fixes

- [\#36](https://github.com/arkworks-rs/algebra/pull/36) (ark-ec) In Short-Weierstrass curves, include an infinity bit in `ToConstraintField`.
- [\#107](https://github.com/arkworks-rs/algebra/pull/107) (ark-serialize) Fix handling of `(de)serialize_uncompressed/unchecked` in various impls of `CanonicalSerialize/Deserialize`.
- [\#112](https://github.com/arkworks-rs/algebra/pull/112) (ark-serialize) Make `bool`s checked serialization methods non-malleable.
- [\#119](https://github.com/arkworks-rs/algebra/pull/119) (ark-poly) Fix bugs in degree calculation if adding/subtracting same degree polynomials
     whose leading coefficients cancel.
- [\#160](https://github.com/arkworks-rs/algebra/pull/160) (ark-serialize, ark-ff, ark-ec) Support serializing when `MODULUS_BITS + FLAG_BITS` is greater than the multiple of 8 just greater than `MODULUS_BITS`, which is the case for the Pasta curves (fixes #47).
- [\#165](https://github.com/arkworks-rs/algebra/pull/165) (ark-ff) Enforce in the type system that an extension fields `BaseField` extends from the correct `BasePrimeField`.
- [\#184](https://github.com/arkworks-rs/algebra/pull/184) Compile with `panic='abort'` in release mode, for safety of the library across FFI boundaries.
- [\#192](https://github.com/arkworks-rs/algebra/pull/192) Fix a bug in the assembly backend for finite field arithmetic.
- [\#217](https://github.com/arkworks-rs/algebra/pull/217) (ark-ec) Fix the definition of `PairingFriendlyCycle` introduced in #190.

## v0.1.0 (Initial release of arkworks/algebra)
