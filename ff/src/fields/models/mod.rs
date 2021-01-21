#[macro_export]
macro_rules! match_const {
    ($fn_name:ident, $N:expr $(, $args:tt)*) => {
        paste::paste! {
            match $N {
                1 => [<$fn_name _ id1>]($($args),*),
                2 => [<$fn_name _ id2>]($($args),*),
                3 => [<$fn_name _ id3>]($($args),*),
                4 => [<$fn_name _ id4>]($($args),*),
                5 => [<$fn_name _ id5>]($($args),*),
                6 => [<$fn_name _ id6>]($($args),*),
                7 => [<$fn_name _ id7>]($($args),*),
                8 => [<$fn_name _ id8>]($($args),*),
                9 => [<$fn_name _ id9>]($($args),*),
                10 => [<$fn_name _ id10>]($($args),*),
                11 => [<$fn_name _ id11>]($($args),*),
                12 => [<$fn_name _ id12>]($($args),*),
                13 => [<$fn_name _ id13>]($($args),*),
                14 => [<$fn_name _ id14>]($($args),*),
                15 => [<$fn_name _ id15>]($($args),*),
                16 => [<$fn_name _ id16>]($($args),*),
                _ => unreachable!(),
            };
        }
    };
}

macro_rules! invoke_16 {
    ($macro_name:ident) => {
        $macro_name!(1);
        $macro_name!(2);
        $macro_name!(3);
        $macro_name!(4);
        $macro_name!(5);
        $macro_name!(6);
        $macro_name!(7);
        $macro_name!(8);
        $macro_name!(9);
        $macro_name!(10);
        $macro_name!(11);
        $macro_name!(12);
        $macro_name!(13);
        $macro_name!(14);
        $macro_name!(15);
        $macro_name!(16);
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
