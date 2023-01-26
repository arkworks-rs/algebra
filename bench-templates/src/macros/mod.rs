#[macro_use]
mod ec;

#[macro_use]
mod field;

#[macro_use]
mod pairing;

#[macro_export]
macro_rules! bench {
    (
        Name = $name:expr,
        Pairing = $Pairing:ident,
        G1 = $G1:ident,
        G2 = $G2:ident,
        ScalarField = $Fr:ident,
        G1BaseField = $Fq:ident,
        G2BaseField = $FqExt:ident,
        TargetField = $FqTarget:ident,
    ) => {
        $crate::ec_bench!($name, $G1);
        $crate::ec_bench!($name, $G2);
        $crate::f_bench!(prime, $name, $Fr);
        $crate::f_bench!(prime, $name, $Fq);
        $crate::f_bench!(extension, $name, $FqExt);
        $crate::f_bench!(target, $name, $FqTarget);
        $crate::pairing_bench!($Pairing);

        paste! {
            criterion_main!(
                [<$G1:lower>]::benches,
                [<$G2:lower>]::benches,
                [<$Fr:lower>]::benches,
                [<$Fq:lower>]::benches,
                [<$FqExt:lower>]::benches,
                [<$FqTarget:lower>]::benches,
                pairing::benches
            );
        }
    };
    (
        Name = $name:expr,
        Group = $G:ident,
        ScalarField = $Fr:ident,
        BaseField = $Fq:ident,
    ) => {
        $crate::ec_bench!($name, $G);
        $crate::f_bench!(prime, $name, $Fr);
        $crate::f_bench!(extension, $name, $Fq);

        paste! {
            criterion_main!(
                [<$G:lower>]::benches,
                [<$Fr:lower>]::benches,
                [<$Fq:lower>]::benches,
            );
        }
    };
    (
        Name = $name:expr,
        Group = $G:ident,
        ScalarField = $Fr:ident,
        PrimeBaseField = $Fq:ident,
    ) => {
        $crate::ec_bench!($name, $G);
        $crate::f_bench!(prime, $name, $Fr);
        $crate::f_bench!(prime, $name, $Fq);

        paste! {
            criterion_main!(
                [<$G:lower>]::benches,
                [<$Fr:lower>]::benches,
                [<$Fq:lower>]::benches,
            );
        }
    };
}
