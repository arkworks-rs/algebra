#[macro_export]
macro_rules! for_loop {
    (($i:ident in $start:tt..$end:tt)  $code:expr ) => {{
        let $i = $start;
        while $i < $end {
            $code
            $i += 1;
        }
    }};
}
