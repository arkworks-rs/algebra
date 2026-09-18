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
            Self::IoError(err) => write!(f, "I/O error: {err:?}"),
        }
    }
}


// Work around current wasm-bindgen limitation:
// https://github.com/wasm-bindgen/wasm-bindgen/issues/5025
#[cfg(all(feature="wasm", not(feature = "std")))]
mod wasm {
    use super::SerializationError;
    use wasm_bindgen::JsError;
    impl From<SerializationError> for JsError {
        fn from(err: SerializationError) -> JsError {
            use ark_std::string::ToString;
            JsError::new(&err.to_string())
        }
    }
}

