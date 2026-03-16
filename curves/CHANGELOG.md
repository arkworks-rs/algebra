# CHANGELOG

## Pending

### Breaking changes

### Features

### Improvements

### Bugfixes

## v0.5.0

### Breaking changes

### Features

- [\#156](https://github.com/arkworks-rs/curves/pull/156) Add the bw6-767 curve.
- [\#174](https://github.com/arkworks-rs/curves/pull/174) Add the "grumpkin" curve.

### Improvements

- [\#156](https://github.com/arkworks-rs/curves/pull/156) The hard part of the final exponentiation for bw6-761 relocated from arkworks/algebra.
- [\#158](https://github.com/arkworks-rs/curves/pull/158) Enabled GLV as the default scalar multiplication for BLS12-377, BLS12-381 and BN254.

### Bugfixes

- [\#176](https://github.com/arkworks-rs/curves/pull/176) Non-canonical infinity point and bad flags in BLS12-381 serialization should fail.

## v0.4.0

- [\#76](https://github.com/arkworks-rs/curves/pull/76) twisted Edwards parameters for bls12-377
- Fixed curve benches

### Breaking changes

- [\#104](https://github.com/arkworks-rs/curves/pull/104) Remove `QUADRATIC_NONRESIDUE` parameter from implementors of `Fp2Config`.
- [\#129](https://github.com/arkworks-rs/curves/pull/129) Implement custom serialization for BLS12-381 for compatibility with the [Zcash lib](https://github.com/zkcrypto/bls12_381).

### Features

- [\#121](https://github.com/arkworks-rs/curves/pull/121) Add the ed25519 curve.
- [\#122](https://github.com/arkworks-rs/curves/pull/122) Add the secp256k1 and secq256k1 curves.
- [\#124](https://github.com/arkworks-rs/curves/pull/124) Add the curve25519 curve.

### Improvements

- [\#70](https://github.com/arkworks-rs/curves/pull/70) Add prepared G2 pairing consistency test.
- [\#74](https://github.com/arkworks-rs/curves/pull/74) Use Scott's subgroup membership tests for `G1` and `G2` of BLS12-381.
- [\#103](https://github.com/arkworks-rs/curves/pull/103) Faster cofactor clearing for BLS12-381.
- [\#107](https://github.com/arkworks-rs/curves/pull/107/) Use 2-NAF of `ATE_LOOP_COUNT` to speed up the Miller loop in MNT curves.
- [\#141](https://github.com/arkworks-rs/curves/pull/141) Faster cofactor clearing for BLS12-377.
- [\#138](https://github.com/arkworks-rs/curves/pull/138) Implement WB Hash-to-Curve for bls12-381 and bls12-377

### Bugfixes

## v0.3.0

### Breaking changes

- [\#60](https://github.com/arkworks-rs/curves/pull/60) Change the scalar group generator of `Fr` of `bls12_377` Fr from `11` to `22`.
- [\#61](https://github.com/arkworks-rs/curves/pull/61) Remove `ATE_LOOP_COUNT_IS_NEGATIVE` from BN254 curve parameter.

### Features

- [\#64](https://github.com/arkworks-rs/curves/pull/64) Implement the Bandersnatch curve, another twisted Edwards curve for BLS12-381.

### Improvements

### Bugfixes

## v0.2.0

### Breaking changes

- Requires all crates from `arkworks-rs/algebra` to have version `v0.2.0` or greater.

### Features

- [\#3](https://github.com/arkworks-rs/curves/pull/3) Add constraints for
        `ark-bls12-377`,
        `ark-ed-on-bls12-377`,
        `ark-ed-on-bls12-381`,
        `ark-ed-on-bn254`,
        `ark-ed-on-cp6-782`,
        `ark-ed-on-bw6-761`,
        `ark-ed-on-mnt4-298`,
        `ark-ed-on-mnt4-753`,
        `ark-mnt4-298`,
        `ark-mnt6-298`,
        `ark-mnt4-753`,
        `ark-mnt6-753`.
- [\#7](https://github.com/arkworks-rs/curves/pull/7) Add benchmarks for Edwards curves.
- [\#19](https://github.com/arkworks-rs/curves/pull/19) Change field constants to be provided as normal strings, instead of in Montgomery form.
- [\#53](https://github.com/arkworks-rs/curves/pull/53) Add benchmarks for Pallas and Vesta curves.

### Improvements

- [\#42](https://github.com/arkworks-rs/curves/pull/42) Remove the dependency of `rand_xorshift`.

### Bugfixes

- [\#28](https://github.com/arkworks-rs/curves/pull/28), [\#49](https://github.com/arkworks-rs/curves/pull/49) Fix broken documentation links.
- [\#38](https://github.com/arkworks-rs/curves/pull/38) Compile with `panic='abort'` in release mode, for safety of the library across FFI boundaries.
- [\#45](https://github.com/arkworks-rs/curves/pull/45) Fix `ark-ed-on-mnt4-753`.

## v0.1.0

Initial Release
