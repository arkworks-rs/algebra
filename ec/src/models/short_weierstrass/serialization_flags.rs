use ark_ff::Field;
use ark_serialize::Flags;

/// Flags to be encoded into the serialization.
/// The default flags (empty) should not change the binary representation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SWFlags {
    /// Represents a point with positive y-coordinate by setting all bits to 0.
    YIsPositive = 0,
    /// Represents the point at infinity by setting the setting the last-but-one bit to 1.
    PointAtInfinity = 1 << 6,
    /// Represents a point with negative y-coordinate by setting the MSB to 1.
    YIsNegative = 1 << 7,
}

impl SWFlags {
    #[inline]
    pub const fn infinity() -> Self {
        Self::PointAtInfinity
    }

    #[inline]
    pub fn from_y_coordinate(y: impl Field) -> Self {
        if y <= -y {
            Self::YIsPositive
        } else {
            Self::YIsNegative
        }
    }

    #[inline]
    pub const fn is_infinity(&self) -> bool {
        matches!(self, Self::PointAtInfinity)
    }

    #[inline]
    pub const fn is_positive(&self) -> Option<bool> {
        match self {
            Self::PointAtInfinity => None,
            Self::YIsPositive => Some(true),
            Self::YIsNegative => Some(false),
        }
    }
}

impl Default for SWFlags {
    #[inline]
    fn default() -> Self {
        // YIsNegative doesn't change the serialization
        Self::YIsNegative
    }
}

impl Flags for SWFlags {
    const BIT_SIZE: usize = 2;

    #[inline]
    fn u8_bitmask(&self) -> u8 {
        let mut mask = 0;
        match self {
            Self::PointAtInfinity => mask |= 1 << 6,
            Self::YIsNegative => mask |= 1 << 7,
            _ => (),
        }
        mask
    }

    #[inline]
    fn from_u8(value: u8) -> Option<Self> {
        let is_negative = (value >> 7) & 1 == 1;
        let is_infinity = (value >> 6) & 1 == 1;
        match (is_negative, is_infinity) {
            // This is invalid because we only want *one* way to serialize
            // the point at infinity.
            (true, true) => None,
            (false, true) => Some(Self::PointAtInfinity),
            (true, false) => Some(Self::YIsNegative),
            (false, false) => Some(Self::YIsPositive),
        }
    }
}
