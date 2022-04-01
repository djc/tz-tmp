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
    /// Date time error
    DateTime(&'static str),
    /// Local time type search error
    FindLocalTimeType(&'static str),
    /// Local time type error
    LocalTimeType(&'static str),
    /// Invalid Tzif file
    InvalidTzFile(&'static str),
    /// Invalid TZ string
    InvalidTzString(&'static str),
    /// I/O error
    Io(io::Error),
    /// Out of range error
    OutOfRange(&'static str),
    /// Integer parsing error
    ParseInt(ParseIntError),
    /// Date time projection error
    ProjectDateTime(&'static str),
    /// System time error
    SystemTime(SystemTimeError),
    /// Time zone error
    TimeZone(&'static str),
    /// Transition rule error
    TransitionRule(&'static str),
    /// Conversion from slice to array error
    TryFromSlice(TryFromSliceError),
    /// Unsupported Tzif file
    UnsupportedTzFile(&'static str),
    /// Unsupported TZ string
    UnsupportedTzString(&'static str),
    /// UTF-8 error
    Utf8(Utf8Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::DateTime(error) => write!(f, "invalid date time: {}", error),
            Self::FindLocalTimeType(error) => error.fmt(f),
            Self::LocalTimeType(error) => write!(f, "invalid local time type: {}", error),
            Self::InvalidTzString(error) => write!(f, "invalid TZ string: {}", error),
            Self::InvalidTzFile(error) => error.fmt(f),
            Self::Io(error) => error.fmt(f),
            Self::OutOfRange(error) => error.fmt(f),
            Self::ParseInt(error) => error.fmt(f),
            Self::ProjectDateTime(error) => error.fmt(f),
            Self::SystemTime(error) => error.fmt(f),
            Self::TransitionRule(error) => write!(f, "invalid transition rule: {}", error),
            Self::TimeZone(error) => write!(f, "invalid time zone: {}", error),
            Self::TryFromSlice(error) => error.fmt(f),
            Self::UnsupportedTzFile(error) => error.fmt(f),
            Self::UnsupportedTzString(error) => write!(f, "unsupported TZ string: {}", error),
            Self::Utf8(error) => error.fmt(f),
        }
    }
}

impl error::Error for Error {}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

impl From<ParseIntError> for Error {
    fn from(error: ParseIntError) -> Self {
        Self::ParseInt(error)
    }
}

impl From<SystemTimeError> for Error {
    fn from(error: SystemTimeError) -> Self {
        Self::SystemTime(error)
    }
}

impl From<TryFromIntError> for Error {
    fn from(_: TryFromIntError) -> Self {
        Self::OutOfRange("out of range integer conversion")
    }
}

impl From<TryFromSliceError> for Error {
    fn from(error: TryFromSliceError) -> Self {
        Self::TryFromSlice(error)
    }
}

impl From<Utf8Error> for Error {
    fn from(error: Utf8Error) -> Self {
        Self::Utf8(error)
    }
}
