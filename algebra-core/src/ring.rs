use crate::{module::ScalarExp, AdditiveGroup};

pub trait Ring:
    AdditiveGroup
    + ScalarExp<u8>
    + ScalarExp<u16>
    + ScalarExp<u32>
    + ScalarExp<u64>
    + ScalarExp<u128>
    + ScalarExp<i8>
    + ScalarExp<i16>
    + ScalarExp<i32>
    + ScalarExp<i64>
    + ScalarExp<i128>
    + for<'a> ScalarExp<&'a [u64]>
{
    /// The order of the additive group.
    const ADDITIVE_ORDER: &'static [u64];

    /// The order of the multiplicative group.
    const MULTIPLICATIVE_ORDER: &'static [u64];
}
