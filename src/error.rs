//! Error types.

use std::array::TryFromSliceError;
use std::num::{ParseIntError, TryFromIntError};
use std::str::Utf8Error;
use std::time::SystemTimeError;
use std::{error, fmt, io};

/// Unified error type for everything in the crate
#[non_exhaustive]
#[derive(Debug)]
pub enum Error {
    /// UTF-8 error
    Utf8Error(Utf8Error),
    /// Conversion from slice to array error
    TryFromSliceError(TryFromSliceError),
    /// I/O error
    IoError(io::Error),
    /// Invalid Tzif file
    InvalidTzFile(&'static str),
    /// System time error
    SystemTimeError(SystemTimeError),
    /// Out of range error
    OutOfRangeError(&'static str),
    /// Local time type error
    LocalTimeTypeError(&'static str),
    /// Transition rule error
    TransitionRuleError(&'static str),
    /// Time zone error
    TimeZoneError(&'static str),
    /// Date time error
    DateTimeError(&'static str),
    /// Local time type search error
    FindLocalTimeTypeError(&'static str),
    /// Date time projection error
    ProjectDateTimeError(&'static str),
    /// Unsupported Tzif file
    UnsupportedTzFile(&'static str),
    /// Integer parsing error
    ParseIntError(ParseIntError),
    /// Invalid TZ string
    InvalidTzString(&'static str),
    /// Unsupported TZ string
    UnsupportedTzString(&'static str),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Utf8Error(error) => error.fmt(f),
            Self::TryFromSliceError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::InvalidTzFile(error) => error.fmt(f),
            Self::SystemTimeError(error) => error.fmt(f),
            Self::OutOfRangeError(error) => error.fmt(f),
            Self::LocalTimeTypeError(error) => write!(f, "invalid local time type: {}", error),
            Self::TransitionRuleError(error) => write!(f, "invalid transition rule: {}", error),
            Self::TimeZoneError(error) => write!(f, "invalid time zone: {}", error),
            Self::DateTimeError(error) => write!(f, "invalid date time: {}", error),
            Self::FindLocalTimeTypeError(error) => error.fmt(f),
            Self::ProjectDateTimeError(error) => error.fmt(f),
            Self::UnsupportedTzFile(error) => error.fmt(f),
            Self::ParseIntError(error) => error.fmt(f),
            Self::InvalidTzString(error) => write!(f, "invalid TZ string: {}", error),
            Self::UnsupportedTzString(error) => write!(f, "unsupported TZ string: {}", error),
        }
    }
}

impl error::Error for Error {}

impl From<Utf8Error> for Error {
    fn from(error: Utf8Error) -> Self {
        Self::Utf8Error(error)
    }
}

impl From<TryFromSliceError> for Error {
    fn from(error: TryFromSliceError) -> Self {
        Self::TryFromSliceError(error)
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::IoError(error)
    }
}

impl From<SystemTimeError> for Error {
    fn from(error: SystemTimeError) -> Self {
        Self::SystemTimeError(error)
    }
}

impl From<ParseIntError> for Error {
    fn from(error: ParseIntError) -> Self {
        Self::ParseIntError(error)
    }
}

impl From<TryFromIntError> for Error {
    fn from(_: TryFromIntError) -> Self {
        Self::OutOfRangeError("out of range integer conversion")
    }
}
