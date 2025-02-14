use ark_std::{fmt, io};

/// This is an error that could occur during serialization
#[derive(Debug)]
pub enum SerializationError {
    /// During serialization, we didn't have enough space to write extra info.
    NotEnoughSpace,
    /// During serialization, the data was invalid.
    InvalidData,
    /// During serialization, non-empty flags were given where none were
    /// expected.
    UnexpectedFlags,
    /// During serialization, we countered an I/O error.
    IoError(io::Error),
}

impl ark_std::error::Error for SerializationError {}

impl From<io::Error> for SerializationError {
    fn from(e: io::Error) -> Self {
        Self::IoError(e)
    }
}

impl fmt::Display for SerializationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::NotEnoughSpace => write!(
                f,
                "the last byte does not have enough space to encode the extra info bits"
            ),
            Self::InvalidData => write!(f, "the input buffer contained invalid data"),
            Self::UnexpectedFlags => write!(f, "the call expects empty flags"),
            Self::IoError(err) => write!(f, "I/O error: {:?}", err),
        }
    }
}
