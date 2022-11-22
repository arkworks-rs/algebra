<h1 align="center">arkworks::algebra</h1>

<p align="center">
    <img src="https://github.com/arkworks-rs/algebra/workflows/CI/badge.svg?branch=master">
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/arkworks-rs/algebra/blob/master/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
    <a href="https://deps.rs/repo/github/arkworks-rs/algebra"><img src="https://deps.rs/repo/github/arkworks-rs/algebra/status.svg"></a>
    <a href="https://discord.gg/UNtS7QXyPk"><img src="https://img.shields.io/discord/908465643727253524?label=Discord&logo=discord"></a>
</p>

The arkworks ecosystem consist of Rust libraries for designing and working with *zero knowledge succinct non-interactive arguments (zkSNARKs)*. This repository contains efficient implementations of the key algebraic components underlying zkSNARKs: finite fields, elliptic curves, and polynomials.

This library is released under the MIT License and the Apache v2 License (see [License](#license)).

**WARNING:** This is an academic proof-of-concept prototype, and in particular has not received careful code review. This implementation is NOT ready for production use.

## Directory structure

This repository contains several Rust crates:  

* [`ark-ff`](ff): Generic abstractions for, and implementations of various kinds of finite fields
* [`ark-ec`](ec): Generic abstractions for prime-order groups, and implementations of various kinds of (pairing-friendly and standard) elliptic curves
* [`ark-poly`](poly): Interfaces for univariate, multivariate, and multilinear polynomials, and FFTs over finite fields
* [`ark-serialize`](serialize): Efficient interfaces for serialization and point compression for finite fields and elliptic curves

In addition, the [`curves`](https://github.com/arkworks-rs/curves) repository contains concrete implementations of popular elliptic curves; see [here](https://github.com/arkworks-rs/curves/README.md) for details.

## Build guide

The library compiles on the `stable` toolchain of the Rust compiler (v 1.51+). To install the latest version of Rust, first install `rustup` by following the instructions [here](https://rustup.rs/), or via your platform's package manager. Once `rustup` is installed, install the Rust toolchain by invoking:

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

## Assembly backend for field arithmetic

The `ark-ff` crate contains (off-by-default) optimized assembly implementations of field arithmetic that rely on the `adcxq`, `adoxq` and `mulxq` instructions. These are available on most `x86_64` platforms (Broadwell onwards for Intel and Ryzen onwards for AMD). Using this backend can lead to a 30-70% speedup in finite field and elliptic curve arithmetic. To build with this backend enabled, run the following command:

```bash
RUSTFLAGS="-C target-feature=+bmi2,+adx" cargo +nightly [test/build/bench] --features asm
```

To enable this in the `Cargo.toml` of your own projects, enable the `asm` feature flag:

```toml
ark-ff = { version = "0.4", features = [ "asm" ] }
```

Note that because inline assembly support in Rust is currently unstable, using this backend requires using the Nightly compiler at the moment.

## License

The crates in this repository are licensed under either of the following licenses, at your discretion.

* Apache License Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or [apache.org license link](http://www.apache.org/licenses/LICENSE-2.0))
* MIT license ([LICENSE-MIT](LICENSE-MIT) or [opensource.org license link](http://opensource.org/licenses/MIT))

Unless you explicitly state otherwise, any contribution submitted for inclusion in this library by you shall be dual licensed as above (as defined in the Apache v2 License), without any additional terms or conditions.

[zexe]: https://ia.cr/2018/962

## Acknowledgements

This work was supported by:
a Google Faculty Award;
the National Science Foundation;
the UC Berkeley Center for Long-Term Cybersecurity;
and donations from the Ethereum Foundation, the Interchain Foundation, and Qtum.

An earlier version of this library was developed as part of the paper *"[ZEXE: Enabling Decentralized Private Computation][zexe]"*.
