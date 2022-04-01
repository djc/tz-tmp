//! Error types.

use std::array::TryFromSliceError;
use std::num::{ParseIntError, TryFromIntError};
use std::str::Utf8Error;
use std::time::SystemTimeError;
use std::{error, fmt, io};

/// Unified error type for parsing a TZ string
#[non_exhaustive]
#[derive(Debug)]
pub enum TzStringError {
    /// UTF-8 error
    Utf8Error(Utf8Error),
    /// Integer parsing error
    ParseIntError(ParseIntError),
    /// I/O error
    IoError(io::Error),
    /// Invalid TZ string
    InvalidTzString(&'static str),
    /// Unsupported TZ string
    UnsupportedTzString(&'static str),
}

impl fmt::Display for TzStringError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Utf8Error(error) => error.fmt(f),
            Self::ParseIntError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::InvalidTzString(error) => write!(f, "invalid TZ string: {}", error),
            Self::UnsupportedTzString(error) => write!(f, "unsupported TZ string: {}", error),
        }
    }
}

impl error::Error for TzStringError {}

impl From<Utf8Error> for TzStringError {
    fn from(error: Utf8Error) -> Self {
        Self::Utf8Error(error)
    }
}

impl From<ParseIntError> for TzStringError {
    fn from(error: ParseIntError) -> Self {
        Self::ParseIntError(error)
    }
}

impl From<io::Error> for TzStringError {
    fn from(error: io::Error) -> Self {
        Self::IoError(error)
    }
}

/// Unified error type for parsing a TZif file
#[non_exhaustive]
#[derive(Debug)]
pub enum TzFileError {
    /// Conversion from slice to array error
    TryFromSliceError(TryFromSliceError),
    /// I/O error
    IoError(io::Error),
    /// Unified error for parsing a TZ string
    TzStringError(TzStringError),
    /// Invalid TZif file
    InvalidTzFile(&'static str),
    /// Unsupported TZif file
    UnsupportedTzFile(&'static str),
}

impl fmt::Display for TzFileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::TryFromSliceError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::TzStringError(error) => error.fmt(f),
            Self::InvalidTzFile(error) => write!(f, "invalid TZ file: {}", error),
            Self::UnsupportedTzFile(error) => write!(f, "unsupported TZ file: {}", error),
        }
    }
}

impl error::Error for TzFileError {}

impl From<TryFromSliceError> for TzFileError {
    fn from(error: TryFromSliceError) -> Self {
        Self::TryFromSliceError(error)
    }
}

impl From<io::Error> for TzFileError {
    fn from(error: io::Error) -> Self {
        Self::IoError(error)
    }
}

impl From<TzStringError> for TzFileError {
    fn from(error: TzStringError) -> Self {
        Self::TzStringError(error)
    }
}

macro_rules! create_error {
    (#[$doc:meta], $name:ident) => {
        #[$doc]
        #[derive(Debug)]
        pub struct $name(
            /// Error description
            pub &'static str,
        );

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                self.0.fmt(f)
            }
        }

        impl error::Error for $name {}
    };
}

create_error!(#[doc = "Out of range error"], OutOfRangeError);
create_error!(#[doc = "Local time type error"], LocalTimeTypeError);
create_error!(#[doc = "Transition rule error"], TransitionRuleError);
create_error!(#[doc = "Time zone error"], TimeZoneError);
create_error!(#[doc = "Date time error"], DateTimeError);
create_error!(#[doc = "Local time type search error"], FindLocalTimeTypeError);
create_error!(#[doc = "Date time projection error"], ProjectDateTimeError);

impl From<OutOfRangeError> for ProjectDateTimeError {
    fn from(error: OutOfRangeError) -> Self {
        Self(error.0)
    }
}

impl From<FindLocalTimeTypeError> for ProjectDateTimeError {
    fn from(error: FindLocalTimeTypeError) -> Self {
        Self(error.0)
    }
}

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
    /// System time error
    SystemTimeError(SystemTimeError),
    /// Unified error for parsing a TZif file
    TzFileError(TzFileError),
    /// Unified error for parsing a TZ string
    TzStringError(TzStringError),
    /// Out of range error
    OutOfRangeError(OutOfRangeError),
    /// Local time type error
    LocalTimeTypeError(LocalTimeTypeError),
    /// Transition rule error
    TransitionRuleError(TransitionRuleError),
    /// Time zone error
    TimeZoneError(TimeZoneError),
    /// Date time error
    DateTimeError(DateTimeError),
    /// Local time type search error
    FindLocalTimeTypeError(FindLocalTimeTypeError),
    /// Date time projection error
    ProjectDateTimeError(ProjectDateTimeError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Utf8Error(error) => error.fmt(f),
            Self::TryFromSliceError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::SystemTimeError(error) => error.fmt(f),
            Self::TzFileError(error) => error.fmt(f),
            Self::TzStringError(error) => error.fmt(f),
            Self::OutOfRangeError(error) => error.fmt(f),
            Self::LocalTimeTypeError(error) => write!(f, "invalid local time type: {}", error),
            Self::TransitionRuleError(error) => write!(f, "invalid transition rule: {}", error),
            Self::TimeZoneError(error) => write!(f, "invalid time zone: {}", error),
            Self::DateTimeError(error) => write!(f, "invalid date time: {}", error),
            Self::FindLocalTimeTypeError(error) => error.fmt(f),
            Self::ProjectDateTimeError(error) => error.fmt(f),
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

impl From<TzFileError> for Error {
    fn from(error: TzFileError) -> Self {
        Self::TzFileError(error)
    }
}

impl From<TzStringError> for Error {
    fn from(error: TzStringError) -> Self {
        Self::TzStringError(error)
    }
}

impl From<OutOfRangeError> for Error {
    fn from(error: OutOfRangeError) -> Self {
        Self::OutOfRangeError(error)
    }
}

impl From<TryFromIntError> for Error {
    fn from(_: TryFromIntError) -> Self {
        Self::OutOfRangeError(OutOfRangeError("out of range integer conversion"))
    }
}

impl From<LocalTimeTypeError> for Error {
    fn from(error: LocalTimeTypeError) -> Self {
        Self::LocalTimeTypeError(error)
    }
}

impl From<TransitionRuleError> for Error {
    fn from(error: TransitionRuleError) -> Self {
        Self::TransitionRuleError(error)
    }
}

impl From<TimeZoneError> for Error {
    fn from(error: TimeZoneError) -> Self {
        Self::TimeZoneError(error)
    }
}

impl From<DateTimeError> for Error {
    fn from(error: DateTimeError) -> Self {
        Self::DateTimeError(error)
    }
}

impl From<FindLocalTimeTypeError> for Error {
    fn from(error: FindLocalTimeTypeError) -> Self {
        Self::FindLocalTimeTypeError(error)
    }
}

impl From<ProjectDateTimeError> for Error {
    fn from(error: ProjectDateTimeError) -> Self {
        Self::ProjectDateTimeError(error)
    }
}
