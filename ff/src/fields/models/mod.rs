macro_rules! limb_instantiation {
    ($($n_limbs:expr),*) => {
        macro_rules! make_nested_macro {
            ($d:tt) => {
                macro_rules! match_const {
                    ($fn_name:ident, $N:expr $d(, $d args:tt)*) => {
                        paste::paste! {
                            match $N {
                                $($n_limbs => [<$fn_name _ id$n_limbs>]::<P, N>($d($d args),*),)*
                                _ => unreachable!(),
                            };
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

pub type Fp64<P> = Fp<P, 1>;
pub type Fp256<P> = Fp<P, 4>;
pub type Fp320<P> = Fp<P, 5>;
pub type Fp384<P> = Fp<P, 6>;
pub type Fp768<P> = Fp<P, 12>;
pub type Fp832<P> = Fp<P, 13>;

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
pub use cubic_extension::*;
