#[macro_export]
macro_rules! n_fold {
    ($tmp:ident, $v:ident, $func:ident, $count:ident) => {
        $tmp.$func(&$v[$count].1);
    };

    ($tmp:ident, $func:ident) => {
        $tmp.$func();
    };
}

/// Defines a function called `$group_name` that returns the test description
/// values for the listed functions `$function`.
#[macro_export]
macro_rules! benchmark_group {
    ($group_name:ident, $($function:path),+) => {
        pub fn $group_name() -> ::std::vec::Vec<$crate::TestDescAndFn> {
            use $crate::{TestDescAndFn, TestFn, TestDesc};
            use std::borrow::Cow;
            let mut benches = ::std::vec::Vec::new();
            $(
                benches.push(TestDescAndFn {
                    desc: TestDesc {
                        name: Cow::from(module_path!().to_string() + "::" + stringify!($function)),
                        ignore: false,
                    },
                    testfn: TestFn::StaticBenchFn($function),
                });
            )+
            benches
        }
    };
    ($group_name:ident, $($function:path,)+) => {
        benchmark_group!($group_name, $($function),+);
    };
}
