# CHANGELOG

## Pending

### Breaking changes

- [\#300](https://github.com/arkworks-rs/algebra/pull/300) (`ark-ec`) Change the implementation of `Hash` trait of `GroupProjective` to use the affine coordinates.
- [\#302](https://github.com/arkworks-rs/algebra/pull/302) (`ark-ff`) Rename `find_wnaf` to `find_naf`.
- [\#310](https://github.com/arkworks-rs/algebra/pull/310) (`ark-ec`, `ark-ff`) Remove unnecessary internal `PhantomData`.
- [\#333](https://github.com/arkworks-rs/algebra/pull/333) (`ark-poly`) Expose more properties of `EvaluationDomain`s.
- [\#338](https://github.com/arkworks-rs/algebra/pull/338) (`ark-ec`) Add missing `UniformRand` trait bound to `GroupAffine`.
- [\#338](https://github.com/arkworks-rs/algebra/pull/338) (workspace) Change to Rust 2021 edition.
- [\#345](https://github.com/arkworks-rs/algebra/pull/345) (`ark-ec`, `ark-serialize`) Change the serialization format for Twisted Edwards Curves. We now encode the Y coordinate and take the sign bit of the X coordinate, the default flag is also now the Positive X value. The old methods for backwards compatibility are located [here](https://github.com/arkworks-rs/algebra/pull/345/files#diff-3621a48bb33f469144044d8d5fc663f767e103132a764812cda6be6c25877494R860)
- [\#348](https://github.com/arkworks-rs/algebra/pull/348) (`ark-ec`) Rename `msm:{Fixed,Variable}BaseMSM:multi_scalar_mul` to `msm:{Fixed,Variable}:msm` to avoid redundancy.
- [\#359](https://github.com/arkworks-rs/algebra/pull/359) (`ark-test-templates`) Simplify the field and curve test macros.
- [\#365](https://github.com/arkworks-rs/algebra/pull/365) (`ark-ec`)
    - Move `COFACTOR`, `COFACTOR_INV`, and `is_in_correct_subgroup_assuming_on_curve()` from `{SW,TE}CurveConfig` to `CurveConfig`.
    - Add `mul_bits()` to `AffineCurve` and provide a default implementation of `mul()` using this.
    - Remove duplicate function `scale_by_cofactor()` from `short_weierstrass::GroupAffine` and `twisted_edwards_extended::GroupAffine`
- [\#370](https://github.com/arkworks-rs/algebra/pull/370) (all) Set the minimum `rust-version = 1.56` in the manifests of all crates.
- [\#379](https://github.com/arkworks-rs/algebra/pull/379) (`ark-ff`) Refactor `Field` implementation and `PrimeField` trait:
    - Switch from hardcoded `FpXYZ` to `Fp<N>` based on `const` generics.
    - Move Montgomery arithmetic to an optional backend.
    - Rename `field_new` macros to `MontFp`, `QuadExt` and `CubicExt` macros.
    - Introduce `const fn`s for generating many constants.
    - Add default associated constants to reduce boilerplate.
    - Rename `Fp*Parameters` to `Fp*Config`.
    - Add `From<u32>`, `From<u16>`, and `From<u8>` `impl`s for `BigInt<N>`.
    - Remove `FftConfig`; move its contents to `FftField`.
- [\#383](https://github.com/arkworks-rs/algebra/pull/383) (`ark-ff`) Rename `BigInteger::add_nocarry` to `add_with_carry` and `sub_noborrow` to `sub_with_borrow`.
- [\#386](https://github.com/arkworks-rs/algebra/pull/386) (`ark-ff`) Remove `PrimeField::GENERATOR`, since it already exists on `FftField`.
- [\#393](https://github.com/arkworks-rs/algebra/pull/393) (`ark-ec`, `ark-ff`) Rename `FpXParams` to `FpXConfig` and `FpXParamsWrapper` to `FpXConfigWrapper`.
- [\#396](https://github.com/arkworks-rs/algebra/pull/396) (`ark-ec`) Remove `mul_bits` feature, and remove default implementations of `mul` and `mul_by_cofactor_to_projective`.
- [\#408](https://github.com/arkworks-rs/algebra/pull/408) (`ark-ff`) Change the output of `Display` formatting for BigInt & Fp from hex to decimal.
- [\#412](https://github.com/arkworks-rs/algebra/pull/412) (`ark-poly`) Rename UV/MVPolynomial to DenseUV/MVPolynomial.
- [\#417](https://github.com/arkworks-rs/algebra/pull/417) (`ark-ff`) Remove `ToBytes` and `FromBytes`.
- [\#418](https://github.com/arkworks-rs/algebra/pull/418) (`ark-ff`) Add `sums_of_products` to `Field` and `Fp`
- [\#422](https://github.com/arkworks-rs/algebra/pull/422) (`ark-ff`) Remove `SquareRootField`, and move functionality to `Field`
- [\#425](https://github.com/arkworks-rs/algebra/pull/425) (`ark-ec`) Refactor `VariableBase` struct to `VariableBaseMSM` trait and implement it for `GroupProjective`.
- [\#438](https://github.com/arkworks-rs/algebra/pull/438) (`ark-ec`) Rename modules, structs, and traits related to `ec`.
    - `short_weierstrass_jacobian` → `short_weierstrass`
    - `twisted_edwards_extend` → `twisted_edwards`
    - `GroupAffine` → `Affine`
    - `GroupProjective` → `Projective`
    - `ModelParameters` → `CurveConfig`
    - `SWModelParameters` → `SWCurveConfig`
    - `TEModelParameters` → `TECurveConfig`
    - `MontgomeryModelParameters` → `MontCurveConfig`
- [\#440](https://github.com/arkworks-rs/algebra/pull/440) (`ark-ff`) Add a method to construct a field element from an element of the underlying base prime field.
- [\#443](https://github.com/arkworks-rs/algebra/pull/443), [\#449](https://github.com/arkworks-rs/algebra/pull/449) (`ark-ec`) Improve ergonomics of scalar multiplication.
    - Rename `ProjectiveCurve::mul(AsRef[u64])` to `ProjectiveCurve::mul_bigint(AsRef[u64])`.
    - Bound `ProjectiveCurve` by
        - `Mul<ScalarField>`,
        - `for<'a> Mul<&'a ScalarField>`
        - `MulAssign<ScalarField>`,
        - `for<'a> MulAssign<&'a ScalarField>`
    - Bound `AffineCurve` by
        - `Mul<ScalarField, Output = ProjectiveCurve>`
        - `for<'a> Mul<&'a ScalarField, Output = ProjectiveCurve>`
- [\#445](https://github.com/arkworks-rs/algebra/pull/445) (`ark-ec`) Change the `ATE_LOOP_COUNT` in MNT4/6 curves to use 2-NAF.
- [\#446](https://github.com/arkworks-rs/algebra/pull/446) (`ark-ff`) Add `CyclotomicMultSubgroup` trait and implement it for extension fields
- [\#447](https://github.com/arkworks-rs/algebra/pull/447) (`ark-ec`, `ark-algebra-test-templates`) Rename and refactor group infrastructure, and test infrastructure for fields, groups, and pairings:
    - Create new `Group` trait and move some functionality from `ProjectiveCurve` to it.
    - Rename `ProjectiveCurve` to `CurveGroup: Group`.
        - Rename some associated types:
            - `AffineCurve` → `Affine`
        - Rename some methods:
            - `batch_normalization_into_affine` → `normalize_batch`
    - Rename `AffineCurve` to `Affine`.
        - Rename associated types:
            - `Projective` → `Group`
        - Add methods:
            - Add method `fn x(&self) -> Self::BaseField` that returns the x coordinate of the point.
            - Add method `fn y(&self) -> Self::BaseField` that returns the y coordinate of the point.
        - Rename methods:
            - `zero()` → `identity()`
            - `is_zero()` → `is_identity()`
            - `into_projective()` → `into_group()`
    - Add new `ScalarMul` trait that encapsulates scalar multiplication routines for arbitrary `Group`s.
        - `ScalarMul` trait has a `MulBase` associated type to encapsulate bases for variable base and fixed-base scalar multiplication algorithms.
        - `ScalarMul` requires `Add<Self::MulBase, Output = Self>`, `AddAssign<Self::MulBase>`, and `From<Self::MulBase>`.
    - Rename `PairingEngine` to `Pairing`:
        - Rename associated types:
            - `Fr` → `ScalarField`
            - `G1Projective` → `G1`
            - `G2Projective` → `G2`
            - `Fqk` → `TargetField: CyclotomicMultSubgroup`
        - Remove associated type `Fqe`.
        - Rename methods:
            - `miller_loop` → `multi_miller_loop`
            - `pairing` → `multi_pairing`
        - Change method signatures:
            - `product_of_pairings` -> `multi_pairing`
                - take two references to element iterators instead of an iterator of tuples.
            - `miller_loop` and `multi_miller_loop` now
                - take two iterators over `impl Into<G1Prepared>` and `impl Into<G2Prepared>` as input, and
                - output `MillerLoopOutput`, which is a newtype wrapper around `TargetField`.
            - `final_exponentiation` now
                - takes as input a `MillerLoopOutput`,
                - outputs `PairingOutput`, which is a newtype around `TargetField`, and which implements `Group` and `ScalarMul`, allowing it to be used with the existing MSM infrastructure.
            - Pairings, which are the composition of Miller loops and final exponentiation, are changed accordingly.
    - `ark-algebra-test-templates` macro syntax is now simplified; see the test files in `test-curves` for examples.
- [\#463](https://github.com/arkworks-rs/algebra/pull/463) (`ark-serialize`, `ark-ff`, `ark-ec`) Refactor serialization infrastructure to enable more flexibility and less repetition of code:
    - New `enum Compress` that indicates whether point compression should be enabled or not.
    - New `enum Validate` that indicates whether type-specific validation checks should be carried out or not.
    - New `trait Valid` that provides methods for checking whether a deserialized value of a given type passes appropriate validation checks. The trait has the following methods
        - `check` which checks a single value, and
        - `batch_check` which checks a batch of values.
    - `CanonicalSerialize`:
        - New signature for `serialize` that takes in an argument `compress: Compress`
        - Old `serialize` → `serialize_compressed`
        - `serialize_uncompressed` → `serialize_uncompressed`
        - Every method has a default implementation that calls `serialize` with the appropriate `compress` value.
    - `CanonicalDeserialize`:
        - All types implementing
        - New signature for `deserialize` that takes in arguments `compress: Compress` and `validate: Validate`.
        - `deserialize` → `deserialize_compressed`
        - `deserialize_uncompressed` → `deserialize_uncompressed`
        - `deserialize_unchecked` → `deserialize_uncompressed_unchecked`
        - New method `deserialize_compressed_unchecked` that performs decompression but skips validation checks.
        - Every method has a default implementation that calls `deserialize` with the appropriate `compress` and `validate` values.
    - The `SWFlags` enum has been moved to `ark_ec::models::short_weierstrass`, and has had its variants renamed to be somewhat more descriptive.
    - The `EdwardsFlags` enum has been moved to `ark_ec::models::twisted_edwards`, has been renamed to `TEFlags`, and has had its variants renamed to be somewhat more descriptive.
    - New serialization format for Short Weierstrass curves:
        - Points with a "positive" y-coordinate are serialized with the sign bit set to zero (as opposed to the sign bit set to one in the old behavior).
        - Points with a "negative" y-coordinate are serialized with the sign bit set to one (as opposed to the sign bit set to zero in the old behavior).
        - The point at infinity is serialized with the infinity flag set to one.
    - New serialization format for Twisted Edwards curves:
        - Points with a "positive" x-coordinate are serialized with the sign bit set to zero.
        - Points with a "negative" x-coordinate are serialized with the sign bit set to one.
- [\#487](https://github.com/arkworks-rs/algebra/pull/487) (`ark-poly`) Refactor `EvaluationDomain` trait for cosets:
    - Remove method `generator_inv`.
    - Remove method `divide_by_vanishing_poly_on_coset_in_place`.
    - Remove coset fft methods: `coset_fft`, `coset_fft_in_place`, `coset_ifft`, `coset_ifft_in_place`.
- [\#492](https://github.com/arkworks-rs/algebra/pull/492) (`ark-ff`) Refactor `ark-ff` APIs:
    - Splits the contents of `ff/src/fields/mod.rs` into smaller files for easier management.
    - Moves `BitIterator` out of `ark_ff::fields` and into `ark_ff` directly.
    - Adds `impl<'a, 'b> Add/Sub/Mul/Div<&'a F> for &'b F`

### Features

- [\#301](https://github.com/arkworks-rs/algebra/pull/301) (`ark-ec`) Add `GLVParameters` trait definition.
- [\#312](https://github.com/arkworks-rs/algebra/pull/312) (`ark-ec`) Add `is_in_correct_subgroup_assuming_on_curve` for all `Parameters`.
- [\#321](https://github.com/arkworks-rs/algebra/pull/321) (`ark-ff`) Change bigint conversions to impl `From` instead of `Into`.
- [\#343](https://github.com/arkworks-rs/algebra/pull/343) (`ark-ec`) Add WB and SWU hash-to-curve maps.
- [\#348](https://github.com/arkworks-rs/algebra/pull/348) (`ark-ec`) Add `msm:{Fixed,Variable}Base:msm_checked_len`.
- [\#364](https://github.com/arkworks-rs/algebra/pull/364) (`ark-ec`) Add `ChunkedPippenger` to variable-base MSM.
- [\#371](https://github.com/arkworks-rs/algebra/pull/371) (`ark-serialize`) Add serialization impls for arrays
- [\#386](https://github.com/arkworks-rs/algebra/pull/386) (`ark-ff-macros`, `ark-ff`) Add a macro to derive `MontConfig`.
- [\#396](https://github.com/arkworks-rs/algebra/pull/396) (`ark-ec`) Add a default `mul` function to `{TE,SW}CurveConfig` trait definition.
- [\#397](https://github.com/arkworks-rs/algebra/pull/397) (`ark-ec`) Add `HashMapPippenger` to variable-base MSM.
- [\#418](https://github.com/arkworks-rs/algebra/pull/418) (`ark-ff`) Add `sums_of_products` to `Field` and `Fp`
- [\#420](https://github.com/arkworks-rs/algebra/pull/420) (`ark-ec`) Add a `clear_cofactor` method to `AffineCurve`.
- [\#430](https://github.com/arkworks-rs/algebra/pull/430) (`ark-ec`) Add functionality for mapping a field element to a curve element for hash-to-curve.
- [\#440](https://github.com/arkworks-rs/algebra/pull/440) (`ark-ff`) Add a method to construct a field element from an element of the underlying base prime field.
- [\#446](https://github.com/arkworks-rs/algebra/pull/446) (`ark-ff`) Add `CyclotomicMultSubgroup` trait and impl for extension fields
- [\#467](https://github.com/arkworks-rs/algebra/pull/467) (`ark-ec`)
    - Move implementation of `serialize_with_mode()`, `deserialize_with_mode()`, and `serialized_size()` into `{SW,TE}CurveConfig` to allow customization.
- [\#487](https://github.com/arkworks-rs/algebra/pull/487) (`ark-poly`) Refactor `EvaluationDomain` trait for cosets:
    - Add constructor `new_coset`.
    - Add convenience method `get_coset`.
    - Add methods `coset_offset`, `coset_offset_inv` and `coset_offset_pow_size`.

### Improvements

- [\#302](https://github.com/arkworks-rs/algebra/pull/302) (`ark-ff`) Add the relaxed NAF computation.
- [\#306](https://github.com/arkworks-rs/algebra/pull/306) (`ark-ff`, `ark-ff-asm`) Make the assembly backend available on `stable`.
- [\#339](https://github.com/arkworks-rs/algebra/pull/339) (`ark-ff`) Remove duplicated code from `test_field` module and replace its usage with `ark-test-curves` crate.
- [\#352](https://github.com/arkworks-rs/algebra/pull/352) (`ark-ff`) Update `QuadExtField::sqrt` for better performance.
- [\#357](https://github.com/arkworks-rs/algebra/pull/357) (`ark-poly`) Speedup division by vanishing polynomials for dense polynomials.
- [\#445](https://github.com/arkworks-rs/algebra/pull/445) (`ark-ec`) Use 2-NAF for ate pairing in MNT4/6 curves.

### Bugfixes

- [\#350](https://github.com/arkworks-rs/algebra/pull/350) (`ark-serialize`) Fix issues with hygiene whenever a non-standard `Result` type is in scope.
- [\#358](https://github.com/arkworks-rs/algebra/pull/358) (`ark-ff`) Fix the bug for `QuadExtField::sqrt` when `c1 = 0 && c0.legendre.is_qnr()`
- [\#366](https://github.com/arkworks-rs/algebra/pull/366) (`ark-ff`) Fix `norm()` for cubic extension field towers.
- [\#394](https://github.com/arkworks-rs/algebra/pull/394) (`ark-ff`, `ark-serialize`) Remove `EmptyFlags` construction checks.
- [\#442](https://github.com/arkworks-rs/algebra/pull/442) (`ark-ff`) Fix deserialization for modulo with 64 shaving bits.
- [\#460](https://github.com/arkworks-rs/algebra/pull/460) (`ark-ec`) Fix a corner case for ate pairing in BLS12 and BW6 models.

## v0.3.0

### Breaking changes

- [\#285](https://github.com/arkworks-rs/algebra/pull/285) (`ark-ec`) Remove `ATE_LOOP_COUNT_IS_NEGATIVE` from BN curve parameter trait.
- [\#292](https://github.com/arkworks-rs/algebra/pull/292) (`ark-ec`) Remove `CycleEngine`.
- [\#293](https://github.com/arkworks-rs/algebra/pull/293) (`ark-ff`) Remove `ark_ff::test_rng`.

### Features

- [\#230](https://github.com/arkworks-rs/algebra/pull/230) (`ark-ec`) Add `wnaf_mul` implementation for `ProjectiveCurve`.
- [\#245](https://github.com/arkworks-rs/algebra/pull/245) (`ark-poly`) Speedup the sequential and parallel radix-2 FFT and IFFT significantly by making the method in which it accesses roots more cache-friendly.
- [\#258](https://github.com/arkworks-rs/algebra/pull/258) (`ark-poly`) Add `Mul<F>` implementation for `DensePolynomial`.
- [\#259](https://github.com/arkworks-rs/algebra/pull/259) (`ark-poly`) Add `Mul<F>` implementation for `SparsePolynomial` and `Add<SparsePolynomial<F>>/Sub<SparsePolynomial<F>>` for `DensePolynomial`.
- [\#261](https://github.com/arkworks-rs/algebra/pull/261) (`ark-ff`) Add support for 448-bit integers and fields.
- [\#263](https://github.com/arkworks-rs/algebra/pull/263) (`ark-ff`) Add `From<iXXX>` implementations to fields.
- [\#265](https://github.com/arkworks-rs/algebra/pull/265) (ark-serialize) Add hashing as an extension trait of `CanonicalSerialize`.
- [\#280](https://github.com/arkworks-rs/algebra/pull/280) (`ark-ff`) Add `Into<BigUint>` and `From<BigUint>` implementations to `BigInteger` and `PrimeField`.
- [\#289](https://github.com/arkworks-rs/algebra/pull/289) (`ark-ec`) Add `Sum` implementation for all `AffineCurve`.

### Improvements

- [\#279](https://github.com/arkworks-rs/algebra/pull/279) (`ark-ec`) Parallelize miller loop operations for BLS12.

### Bugfixes

- [\#252](https://github.com/arkworks-rs/algebra/pull/252) (`ark-ff`) Fix prime field sampling when `REPR_SHIFT_BITS` is 64.
- [\#284](https://github.com/arkworks-rs/algebra/pull/284) (`ark-poly-benches`) Fix the panic `subgroup_fft_in_place` benchmark for MNT6-753's Fr.

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

- [\#20](https://github.com/arkworks-rs/algebra/pull/20) (`ark-poly`) Move univariate DensePolynomial and SparsePolynomial into a
    univariate sub-crate. Make this change by:
    find w/ regular expression `ark_poly::(Dense|Sparse)Polynomial`, and replace with `ark_poly::univariate::$1Polynomial`.
- [\#36](https://github.com/arkworks-rs/algebra/pull/36) (`ark-ec`) In Short-Weierstrass curves, include an infinity bit in `ToConstraintField`.
- [\#37](https://github.com/arkworks-rs/algebra/pull/37) (`ark-poly`) In the `Polynomial` trait, add `Hash` trait bound to `Point`.
- [\#38](https://github.com/arkworks-rs/algebra/pull/38) (`ark-poly`) Add `Add` and `Neg` trait bounds to `Polynomial`.
- [\#51](https://github.com/arkworks-rs/algebra/pull/51) (`ark-ff`) Removed `unitary_inverse` from `QuadExtField`. Make this change by
    replacing `x.unitary_inverse()` with `let mut tmp = x.clone(); tmp.conjugate()`.
- [\#53](https://github.com/arkworks-rs/algebra/pull/53) (`ark-poly`) Add `Zero` trait bound to `Polynomial`.
- [\#96](https://github.com/arkworks-rs/algebra/pull/96) (`ark-ff`) Make the `field_new` macro accept values in integer form, without requiring decomposition into limbs, and without requiring encoding in Montgomery form.
- [\#106](https://github.com/arkworks-rs/algebra/pull/106) (`ark-ff`, `ark-ec`) Add `Zeroize` trait bound to `Field, ProjectiveGroup, AffineGroup` traits.
- [\#108](https://github.com/arkworks-rs/algebra/pull/108) (`ark-ff`) Add `extension_degree()` method to `Field`.
- [\#110](https://github.com/arkworks-rs/algebra/pull/110) (`ark-ec`) Change the trait bound on the scalar for `mul`, from (essentially) `Into<BigInt>` to `AsRef<[u64]>`.
- [\#117](https://github.com/arkworks-rs/algebra/pull/117) (`ark-poly`) Make the univariate `SparsePolynomial` implement `Polynomial`. Make this change
    by replacing `sparse_poly.evaluate(pt)` to `sparse_poly.evaluate(&pt)`.
- [\#129](https://github.com/arkworks-rs/algebra/pull/129) (`ark-ff`) Move `ark_ff::{UniformRand, test_rng}` to `ark_std::{UniformRand, test_rng}`.
    Importing these from `ark-ff` is still possible, but is deprecated and will be removed in the following release.
- [\#144](https://github.com/arkworks-rs/algebra/pull/144) (`ark-poly`) Add `CanonicalSerialize` and `CanonicalDeserialize` trait bounds for `Polynomial`.
- [\#160](https://github.com/arkworks-rs/algebra/pull/160) (`ark-serialize`, `ark-ff`, `ark-ec`)
    - Remove `ConstantSerializedSize`; users should use `serialized_size*` (see next).
    - Add `serialized_size_with_flags` method to `CanonicalSerializeWithFlags`.
    - Change `from_random_bytes_with_flags` to output `ark_serialize::Flags`.
    - Change signatures of `Flags::from_u8*` to output `Option`.
    - Change `Flags::from_u8*` to be more strict about the inputs it accepts:
      if the top bits of the `u8` value do *not* correspond to one of the possible outputs of `Flags::u8_bitmask`, then these methods output `None`, whereas before they output
      a default value.
    Downstream users other than `ark-curves` should not see breakage unless they rely on these methods/traits explicitly.
- [\#165](https://github.com/arkworks-rs/algebra/pull/165) (`ark-ff`) Add `from_base_field_elements` as a method to the `Field` trait.
- [\#166](https://github.com/arkworks-rs/algebra/pull/166) (`ark-ff`) Change `BigInt::{from_bytes, to_bits}` to `from_bytes_le, from_bytes_be, to_bits_le, to_bits_be`.

### Features

- [\#20](https://github.com/arkworks-rs/algebra/pull/20) (`ark-poly`) Add structs/traits for multivariate polynomials.
- [\#96](https://github.com/arkworks-rs/algebra/pull/96) (`ark-ff`) Make the `field_new` macro accept values in integer form, without requiring decomposition into limbs, and without requiring encoding in Montgomery form.
- [\#106](https://github.com/arkworks-rs/algebra/pull/106) (`ark-ff`, `ark-ec`) Add `Zeroize` trait bound to `Field, ProjectiveGroup, AffineGroup` traits.
- [\#117](https://github.com/arkworks-rs/algebra/pull/117) (`ark-poly`) Add operations to `SparsePolynomial`, so it implements `Polynomial`.
- [\#140](https://github.com/arkworks-rs/algebra/pull/140) (`ark-poly`) Add support for multilinear extensions in dense and sparse evaluation form.
- [\#164](https://github.com/arkworks-rs/algebra/pull/164) (`ark-ff`) Add methods `from_{be, le}_bytes_mod_order` to the `PrimeField` trait.
- [\#197](https://github.com/arkworks-rs/algebra/pull/197) (`ark-test-curves`) Add a BN384 curve with low two-adicity for mixed-radix testing.

### Improvements

- [\#22](https://github.com/arkworks-rs/algebra/pull/22) (`ark-ec`) Speedup fixed-base MSMs.
- [\#28](https://github.com/arkworks-rs/algebra/pull/28) (`ark-poly`) Add `domain()` method on the `evaluations` struct.
- [\#31](https://github.com/arkworks-rs/algebra/pull/31) (`ark-ec`) Speedup point doubling on twisted edwards curves.
- [\#35](https://github.com/arkworks-rs/algebra/pull/35) (`ark-ff`) Implement `ToConstraintField` for `bool`.
- [\#48](https://github.com/arkworks-rs/algebra/pull/48) (`ark-ff`) Speedup `sqrt` on `QuadExtField`.
- [\#94](https://github.com/arkworks-rs/algebra/pull/94) (`ark-ff`) Implement `ToBytes` and `FromBytes` for `u128`.
- [\#99](https://github.com/arkworks-rs/algebra/pull/99) (`ark-poly`) Speedup `evaluate_all_lagrange_coefficients`.
- [\#100](https://github.com/arkworks-rs/algebra/pull/100) (`ark-ff`) Implement `batch_inverse_and_mul`.
- [\#101](https://github.com/arkworks-rs/algebra/pull/101) (`ark-ff`) Add `element(i: usize)` on the `Domain` trait.
- [\#107](https://github.com/arkworks-rs/algebra/pull/107) (`ark-serialize`) Add an impl of `CanonicalSerialize/Deserialize` for `BTreeSet`.
- [\#114](https://github.com/arkworks-rs/algebra/pull/114) (`ark-poly`) Significantly speedup and reduce memory usage of `DensePolynomial.evaluate`.
- [\#114](https://github.com/arkworks-rs/algebra/pull/114), #119 (`ark-poly`) Add infrastructure for benchmarking `DensePolynomial` operations.
- [\#115](https://github.com/arkworks-rs/algebra/pull/115) (`ark-poly`) Add parallel implementation to operations on `Evaluations`.
- [\#115](https://github.com/arkworks-rs/algebra/pull/115) (`ark-ff`) Add parallel implementation of `batch_inversion`.
- [\#122](https://github.com/arkworks-rs/algebra/pull/122) (`ark-poly`) Add infrastructure for benchmarking `FFT`s.
- [\#125](https://github.com/arkworks-rs/algebra/pull/125) (`ark-poly`) Add parallelization to applying coset shifts within `coset_fft`.
- [\#126](https://github.com/arkworks-rs/algebra/pull/126) (`ark-ec`) Use `ark_ff::batch_inversion` for point normalization.
- [\#131](https://github.com/arkworks-rs/algebra/pull/131), #137 (`ark-ff`) Speedup `sqrt` on fields when a square root exists. (And slows it down when doesn't exist.)
- [\#141](https://github.com/arkworks-rs/algebra/pull/141) (`ark-ff`) Add `Fp64`.
- [\#144](https://github.com/arkworks-rs/algebra/pull/144) (`ark-poly`) Add serialization for polynomials and evaluations.
- [\#149](https://github.com/arkworks-rs/algebra/pull/149) (`ark-serialize`) Add an impl of `CanonicalSerialize/Deserialize` for `String`.
- [\#153](https://github.com/arkworks-rs/algebra/pull/153) (`ark-serialize`) Add an impl of `CanonicalSerialize/Deserialize` for `Rc<T>`.
- [\#157](https://github.com/arkworks-rs/algebra/pull/157) (`ark-ec`) Speed up `variable_base_msm` by not relying on unnecessary normalization.
- [\#158](https://github.com/arkworks-rs/algebra/pull/158) (`ark-serialize`) Add an impl of `CanonicalSerialize/Deserialize` for `()`.
- [\#166](https://github.com/arkworks-rs/algebra/pull/166) (`ark-ff`) Add a `to_bytes_be()` and `to_bytes_le` methods to `BigInt`.
- [\#169](https://github.com/arkworks-rs/algebra/pull/169) (`ark-poly`) Improve radix-2 FFTs by moving to a faster algorithm by Riad S. Wahby.
- [\#171](https://github.com/arkworks-rs/algebra/pull/171), #173, #176 (`ark-poly`) Apply significant further speedups to the new radix-2 FFT.
- [\#188](https://github.com/arkworks-rs/algebra/pull/188) (`ark-ec`) Make Short Weierstrass random sampling result in an element with unknown discrete log.
- [\#190](https://github.com/arkworks-rs/algebra/pull/190) (`ark-ec`) Add curve cycle trait and extended pairing cycle trait for all types of ec cycles.
- [\#201](https://github.com/arkworks-rs/algebra/pull/201) (`ark-ec`, `ark-ff`, `ark-test-curves`, `ark-test-templates`) Remove the dependency on `rand_xorshift`.
- [\#205](https://github.com/arkworks-rs/algebra/pull/205) (`ark-ec`, `ark-ff`) Unroll loops and conditionally use intrinsics in `biginteger` arithmetic, and reduce copies in `ff` and `ec` arithmetic.
- [\#207](https://github.com/arkworks-rs/algebra/pull/207) (`ark-ff`) Improve performance of extension fields when the non-residue is negative. (Improves fq2, fq12, and g2 speed on bls12 and bn curves.)
- [\#211](https://github.com/arkworks-rs/algebra/pull/211) (`ark-ec`) Improve performance of BLS12 final exponentiation.
- [\#214](https://github.com/arkworks-rs/algebra/pull/214) (`ark-poly`) Utilise a more efficient way of evaluating a polynomial at a single point.
- [\#242](https://github.com/arkworks-rs/algebra/pull/242), [\#244](https://github.com/arkworks-rs/algebra/pull/244) (`ark-poly`) Speedup the sequential radix-2 FFT significantly by making the method in which it accesses roots more cache-friendly.

### Bugfixes

- [\#36](https://github.com/arkworks-rs/algebra/pull/36) (`ark-ec`) In Short-Weierstrass curves, include an infinity bit in `ToConstraintField`.
- [\#107](https://github.com/arkworks-rs/algebra/pull/107) (`ark-serialize`) Fix handling of `(de)serialize_uncompressed/unchecked` in various impls of `CanonicalSerialize/Deserialize`.
- [\#112](https://github.com/arkworks-rs/algebra/pull/112) (`ark-serialize`) Make `bool`s checked serialization methods non-malleable.
- [\#119](https://github.com/arkworks-rs/algebra/pull/119) (`ark-poly`) Fix bugs in degree calculation if adding/subtracting same degree polynomials
     whose leading coefficients cancel.
- [\#160](https://github.com/arkworks-rs/algebra/pull/160) (`ark-serialize`, `ark-ff`, `ark-ec`) Support serializing when `MODULUS_BITS + FLAG_BITS` is greater than the multiple of 8 just greater than `MODULUS_BITS`, which is the case for the Pasta curves (fixes #47).
- [\#165](https://github.com/arkworks-rs/algebra/pull/165) (`ark-ff`) Enforce in the type system that an extension fields `BaseField` extends from the correct `BasePrimeField`.
- [\#184](https://github.com/arkworks-rs/algebra/pull/184) Compile with `panic='abort'` in release mode, for safety of the library across FFI boundaries.
- [\#192](https://github.com/arkworks-rs/algebra/pull/192) Fix a bug in the assembly backend for finite field arithmetic.
- [\#217](https://github.com/arkworks-rs/algebra/pull/217) (`ark-ec`) Fix the definition of `PairingFriendlyCycle` introduced in #190.

## v0.1.0 (Initial release of arkworks/algebra)
