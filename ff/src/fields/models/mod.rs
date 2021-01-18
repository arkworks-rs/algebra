#[macro_export]
macro_rules! match_const {
    ($macro_name:ident, $N:expr, $($args:tt)*) => {
        match $N {
            1 => $macro_name!(1, $($args)*),
            2 => $macro_name!(2, $($args)*),
            3 => $macro_name!(3, $($args)*),
            4 => $macro_name!(4, $($args)*),
            5 => $macro_name(5, $($args)*),
            6 => $macro_name(6, $($args)*),
            7 => $macro_name(7, $($args)*),
            8 => $macro_name(8, $($args)*),
            9 => $macro_name(9, $($args)*),
            10 => $macro_name(10, $($args)*),
            11 => $macro_name(11, $($args)*),
            12 => $macro_name(12, $($args)*),
            13 => $macro_name(13, $($args)*),
            14 => $macro_name(14, $($args)*),
            15 => $macro_name(15, $($args)*),
            16 => $macro_name(16, $($args)*),
            _ => $macro_name!($N, $($args)*),
        }
    };
}

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
