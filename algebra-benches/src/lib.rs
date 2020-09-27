#![cfg_attr(nightly, feature(test))]
#![allow(unused_macros, unused_imports)]

#[cfg(nightly)]
extern crate test;

#[cfg(all(nightly, test))]
#[macro_use]
pub mod macros;

#[cfg(all(nightly, test))]
mod curves;
