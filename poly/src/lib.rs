//! This crate implements functions for manipulating polynomials over finite
//! fields, including FFTs.
#![cfg_attr(not(feature = "std"), no_std)]
#![forbid(unsafe_code)]
#![allow(clippy::suspicious_op_assign_impl, clippy::suspicious_arithmetic_impl)]

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

#[cfg(doctest)]
mod test_readme {
    macro_rules! external_doc_test {
        ($x:expr) => {
            #[doc = $x]
            extern "C" {}
        };
    }

    external_doc_test!(include_str!("../README.md"));
}
