#![allow(unused_macros, unused_imports)]
#[macro_use]
pub mod macros;
pub use macros::*;

#[macro_use]
pub extern crate criterion;
pub use criterion::*;

pub use paste::paste;
