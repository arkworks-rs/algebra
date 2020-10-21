//! This crate implements functions for manipulating polynomials over finite
//! fields, including FFTs.
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate ark_std;

pub mod domain;

pub mod evaluations;
pub mod polynomial;

pub use domain::{
    EvaluationDomain, GeneralEvaluationDomain, MixedRadixEvaluationDomain, Radix2EvaluationDomain,
};
pub use evaluations::Evaluations;
pub use polynomial::{multivariate, univariate, MVPolynomial, Polynomial, UVPolynomial};

#[cfg(test)]
mod test;
