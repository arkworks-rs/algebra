macro_rules! limb_instantiation {
    ($($n_limbs:expr),*) => {
        macro_rules! make_nested_macro {
            ($d:tt) => {
                macro_rules! match_const {
                    ($d(<$d qn_mark:tt>,)? $d([$d extra_types:ident],)* $fn_name:ident, $N:ident $d(, $d args:tt)*) => {
                        paste::paste! {
                            match $N {
                                $($n_limbs =>
                                    [<$fn_name _ id$n_limbs>]::<P,$d($d extra_types,)* N>(
                                        $d($d args),*)$d($d qn_mark)?,
                                    )*
                                _ => unreachable!(),
                            }
                        }
                    };
                }
            };
        }

        make_nested_macro!($);

        macro_rules! invoke_n {
            ($macro_name:ident) => {
                $($macro_name!($n_limbs);)*
            };
        }
    }
}

limb_instantiation!(1, 4, 5, 6, 12, 13);

pub mod fp;
pub use self::fp::*;

macro_rules! impl_fp_types {
    ($({$limbs:expr, $bits:expr}),*) => {
        paste::paste! {
            $(
                pub type [<Fp $bits>]<P> = Fp<P, $limbs>;
                pub trait [<Fp $bits Parameters>] {}
                impl<T> FpParams<$limbs> for T where T: [<Fp $bits Parameters>] + FpParameters<BigInt = BigInt<$limbs>> {}
            )*
        }
    }
}

impl_fp_types!(
    {1, 64},
    {4, 256},
    {5, 320},
    {6, 384},
    {12, 768},
    {13, 832}
);

pub mod fp2;
pub use self::fp2::*;

pub mod fp3;
pub use self::fp3::*;

pub mod fp4;
pub use self::fp4::*;

pub mod fp6_2over3;

pub mod fp6_3over2;
pub use self::fp6_3over2::*;

pub mod fp12_2over3over2;
pub use self::fp12_2over3over2::*;

pub mod quadratic_extension;
pub use quadratic_extension::*;

pub mod cubic_extension;
use crate::{BigInt, FpParameters};
pub use cubic_extension::*;
