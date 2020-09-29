<h1 align="center">arkworks-algebra</h1>

<p align="center">
    <img src="https://github.com/arkworks-rs/algebra/workflows/CI/badge.svg?branch=master">
    <a href="https://github.com/arkworks-rs/algebra/blob/master/AUTHORS"><img src="https://img.shields.io/badge/authors-arkworks%20contributors-orange.svg"></a>
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
    <a href="https://deps.rs/repo/github/arkworks-rs/algebra"><img src="https://deps.rs/repo/github/arkworks-rs/algebra/status.svg"></a>
</p>

The arkworks ecosystem consist of Rust libraries for designing and working with __zero knowledge succinct non-interactive arguments (SNARKs)__. This repository contains efficient implementations some of the key algebraic concepts underlying zkSNARKs: finite fields, elliptic curves, and polynomials.

This library was initially developed as part of the paper *"[ZEXE: Enabling Decentralized Private Computation][zexe]"*, and it is released under the MIT License and the Apache v2 License (see [License](#license)).

**WARNING:** This is an academic proof-of-concept prototype, and in particular has not received careful code review. This implementation is NOT ready for production use.

## Directory structure

This repository contains several Rust crates for generic arithmetic over finite fields: 

* [`ark-ff`](ff): Provides optimized and generic arithmetic for finite fields
* [`ark-ec`](ec): Provides optimized and generic arithmetic for different kinds of elliptic curves and pairings over these
* [`ark-poly`](poly): Provides optimized arithmetic for polynomials over finite fields via finite field FFTs
* [`ark-serialize`](serialize): Provides efficient serialization and point compression for finite fields and elliptic curves

In addition, the following directories contain implementations of popular elliptic curves:

* [`ark-bls12-377`](bls12-377): Implements the BLS12-377, CP6-782, and BW6-761 curves, as well as "embedded" Twisted Edwards curves over these
* [`ark-bls12-381`](bls12-381): Implements the BLS12-381 and "Jubjub" curves
* [`ark-bn254`](bn254): Implements the BN254 and "Baby Jubjub" curves
* [`ark-mnt-298`](mnt-298): Implements the MNT-298 cycle of pairing-friendly elliptic curves, along with a Twisted Edwards curve "embedded" in MNT4-298
* [`ark-mnt-753`](mnt-753): Implements the MNT-753 cycle of pairing-friendly elliptic curves, along with a Twisted Edwards curve "embedded" in MNT4-753

## Build guide

The library compiles on the `stable` toolchain of the Rust compiler. To install the latest version of Rust, first install `rustup` by following the instructions [here](https://rustup.rs/), or via your platform's package manager. Once `rustup` is installed, install the Rust toolchain by invoking:
```bash
rustup install stable
```

After that, use `cargo`, the standard Rust build tool, to build the libraries:
```bash
git clone https://github.com/arkworks-rs/algebra.git
cd algebra
cargo build --release
```

## Tests
This library comes with comprehensive unit and integration tests for each of the provided crates. Run the tests with:
```bash
cargo test --all
```

## Benchmarks

To run the benchmarks, install the nightly Rust toolchain, via `rustup install nightly`, and then run the following command:
```bash
cargo +nightly bench
```

The standard benchmark framework is insufficiently accurate when benchmarking some finite field arithmetic methods which have execution times on the order of nanoseconds. To increase the accuracy of these benchmarks, one can use the `n_fold` feature to increase the number of iterations. To run with multiple features, make sure to double quote the features.
```bash
cargo +nightly bench --features "n_fold bls12_381"
```

## Assembly backend for field arithmetic

The `ark-ff` crate contains (off-by-default) optimized assembly implementations of field arithmetic that rely on the `adcxq`, `adoxq` and `mulxq` instructions. These are available on most `x86_64` platforms (Broadwell onwards for Intel and Ryzen onwards for AMD). Using this backend can lead to a 30-70% speedup in finite field and elliptic curve arithmetic. To build with this backend enabled, run the following command:
```bash
RUSTFLAGS="-C target-feature=+bmi2,+adx" cargo +nightly test/build/bench --features asm
```

To enable this in the `Cargo.toml` of your own projects, enable the `asm` feature flag:
```
...
ark-ff = { version = "0.1", features = [ "asm" ] }
```
Note that because inline assembly support in Rust is currently unstable, using this backend requires using the Nightly compiler at the moment.

## License

The crates in this repo are licensed under either of the following licenses, at your discretion.

 * Apache License Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

Unless you explicitly state otherwise, any contribution submitted for inclusion in ZEXE by you shall be dual licensed as above (as defined in the Apache v2 License), without any additional terms or conditions.

[zexe]: https://ia.cr/2018/962

## Reference paper

[_ZEXE: Enabling Decentralized Private Computation_][zexe]    
[Sean Bowe](https://www.github.com/ebfull), Alessandro Chiesa, Matthew Green, Ian Miers, [Pratyush Mishra](https://www.github.com/pratyush), [Howard Wu](https://www.github.com/howardwu)    
*IEEE S&P 2020* (*IACR ePrint Report 2018/962*)

## Acknowledgements

This work was supported by:
a Google Faculty Award;
the National Science Foundation;
the UC Berkeley Center for Long-Term Cybersecurity;
and donations from the Ethereum Foundation, the Interchain Foundation, and Qtum.

Some parts of the finite field arithmetic, elliptic curve arithmetic, FFTs, and multi-threading infrastructure have been adapted from code from a prior version of the [`ff`](https://github.com/zkcrypto/ff), [`pairing`](https://github.com/zkcrypto/pairing), and [`bellman`](https://github.com/zkcrypto/bellman) crates, developed by [Sean Bowe](https://www.github.com/ebfull) and others from Zcash.
