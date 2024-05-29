//! This crate implements functions for manipulating polynomials over finite
//! fields, including FFTs.
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    rust_2021_compatibility
)]
#![forbid(unsafe_code)]
#![allow(
    clippy::many_single_char_names,
    clippy::suspicious_op_assign_impl,
    clippy::suspicious_arithmetic_impl
)]

#[macro_use]
extern crate educe;

#[macro_use]
extern crate ark_std;

pub mod domain;

pub mod evaluations;
pub mod polynomial;

pub use domain::{
    EvaluationDomain, GeneralEvaluationDomain, MixedRadixEvaluationDomain, Radix2EvaluationDomain,
};
pub use evaluations::{
    multivariate::multilinear::{
        DenseMultilinearExtension, MultilinearExtension, SparseMultilinearExtension,
    },
    univariate::Evaluations,
};
pub use polynomial::{multivariate, univariate, DenseMVPolynomial, DenseUVPolynomial, Polynomial};

#[cfg(test)]
mod test;

#[rustfmt::skip]
#[cfg(doctest)]
mod test_readme {
  macro_rules! external_doc_test {
    ($x:expr) => {
        #[doc = $x]
        extern {}
    };
  }

  external_doc_test!(include_str!("../README.md"));
}
