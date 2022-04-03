#![deny(missing_docs)]

//! This crate provides the `TimeZone` and `DateTime` types, which can be used to determine local time on a given time zone.
//!
//! This allows to convert between an [Unix timestamp](https://en.wikipedia.org/wiki/Unix_time) and a calendar time exprimed in the [proleptic gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar) with a provided time zone.
//!
//! Time zones are provided to the library with a [POSIX `TZ` string](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html) which can be read from the environment.
//!
//! Two formats are currently accepted for the `TZ` string:
//! * `std offset[dst[offset][,start[/time],end[/time]]]` providing a time zone description,
//! * `file` or `:file` providing the path to a [TZif file](https://datatracker.ietf.org/doc/html/rfc8536), which is absolute or relative to the system timezone directory.
//!
//! See also the [Linux manual page of tzset(3)](https://man7.org/linux/man-pages/man3/tzset.3.html) and the [glibc documentation of the `TZ` environment variable](https://www.gnu.org/software/libc/manual/html_node/TZ-Variable.html).
//!
//! # Usage
//!
//! ## Time zone
//!
//! ```rust
//! # use std::time::SystemTime;
//! #
//! # fn main() -> Result<(), tz::Error> {
//! use tz::TimeZone;
//!
//! // 2000-01-01T00:00:00Z
//! let unix_time = 946684800;
//!
//! // Get UTC time zone
//! let time_zone_utc = TimeZone::utc();
//! assert_eq!(time_zone_utc.find_local_time_type(unix_time)?.offset(), 0);
//!
//! // Get fixed time zone at GMT-1
//! let time_zone_fixed = TimeZone::fixed(-3600)?;
//! assert_eq!(time_zone_fixed.find_local_time_type(unix_time)?.offset(), -3600);
//!
//! // Get local time zone (UNIX only)
//! let time_zone_local = TimeZone::local()?;
//! // Get the current local time type
//! let unix_now = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?.as_secs();
//! let unix_now = match unix_now < i64::max_value() as u64 {
//!     true => unix_now as i64,
//!     false => return Err(tz::Error::OutOfRange("u64 out of range for i64")),
//! };
//! let _current_local_time_type = time_zone_local.find_local_time_type(unix_now)?;
//!
//! // Get time zone from a TZ string:
//! // From an absolute file
//! let _ = TimeZone::from_posix_tz("/usr/share/zoneinfo/Pacific/Auckland");
//! // From a file relative to the system timezone directory
//! let _ = TimeZone::from_posix_tz("Pacific/Auckland");
//! // From a time zone description
//! TimeZone::from_posix_tz("HST10")?;
//! TimeZone::from_posix_tz("<-03>3")?;
//! TimeZone::from_posix_tz("NZST-12:00:00NZDT-13:00:00,M10.1.0,M3.3.0")?;
//! // Use a leading colon to force searching for a corresponding file
//! let _ = TimeZone::from_posix_tz(":UTC");
//! # Ok(())
//! # }
//! ```
//!
//! ## Date time
//!
//! ```rust
//! # use std::time::SystemTime;
//! # fn main() -> Result<(), tz::Error> {
//! use tz::{DateTime, TimeZone, UtcDateTime};
//!
//! // Get the current UTC date time
//! let unix_now = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?.as_secs();
//! let unix_now = match unix_now < i64::max_value() as u64 {
//!     true => unix_now as i64,
//!     false => return Err(tz::Error::OutOfRange("u64 out of range for i64")),
//! };
//! let _current_utc_date_time = UtcDateTime::from_timespec(unix_now, 0)?;
//!
//! // Create a new UTC date time (2000-01-01T00:00:00.123456789Z)
//! let utc_date_time = UtcDateTime::new(2000, 1, 1, 0, 0, 0, 123_456_789)?;
//! assert_eq!(utc_date_time.year(), 2000);
//! assert_eq!(utc_date_time.month(), 1);
//! assert_eq!(utc_date_time.month_day(), 1);
//! assert_eq!(utc_date_time.hour(), 0);
//! assert_eq!(utc_date_time.minute(), 0);
//! assert_eq!(utc_date_time.second(), 0);
//! assert_eq!(utc_date_time.unix_time(), 946684800);
//! assert_eq!(utc_date_time.nanoseconds(), 123_456_789);
//! assert_eq!(utc_date_time.to_string(), "2000-01-01T00:00:00.123456789Z");
//!
//! // Create a new UTC date time from a Unix time with nanoseconds (2000-01-01T00:00:00.123456789Z)
//! let other_utc_date_time = UtcDateTime::from_timespec(946684800, 123_456_789)?;
//! assert_eq!(other_utc_date_time, utc_date_time);
//!
//! // Project the UTC date time to a time zone
//! let date_time = utc_date_time.project(TimeZone::fixed(-3600)?.as_ref())?;
//! assert_eq!(date_time.year(), 1999);
//! assert_eq!(date_time.month(), 12);
//! assert_eq!(date_time.month_day(), 31);
//! assert_eq!(date_time.hour(), 23);
//! assert_eq!(date_time.minute(), 0);
//! assert_eq!(date_time.second(), 0);
//! assert_eq!(date_time.local_time_type().offset(), -3600);
//! assert_eq!(date_time.unix_time(), 946684800);
//! assert_eq!(date_time.nanoseconds(), 123_456_789);
//! assert_eq!(date_time.to_string(), "1999-12-31T23:00:00.123456789-01:00");
//!
//! // Project the date time to another time zone
//! let other_date_time = date_time.project(TimeZone::fixed(3600)?.as_ref())?;
//! assert_eq!(other_date_time.year(), 2000);
//! assert_eq!(other_date_time.month(), 1);
//! assert_eq!(other_date_time.month_day(), 1);
//! assert_eq!(other_date_time.hour(), 1);
//! assert_eq!(other_date_time.minute(), 0);
//! assert_eq!(other_date_time.second(), 0);
//! assert_eq!(other_date_time.local_time_type().offset(), 3600);
//! assert_eq!(other_date_time.unix_time(), 946684800);
//! assert_eq!(other_date_time.nanoseconds(), 123_456_789);
//! assert_eq!(other_date_time.to_string(), "2000-01-01T01:00:00.123456789+01:00");
//!
//! // Create a new date time from a Unix time with nanoseconds and a time zone (2000-01-01T00:00:00.123456789Z)
//! let another_date_time = DateTime::from_timespec(946684800, 123_456_789, TimeZone::fixed(86400)?.as_ref())?;
//!
//! // DateTime objects are compared by their Unix time and nanoseconds
//! assert_eq!(another_date_time, other_date_time);
//!
//! // Get the current date time at the local time zone (UNIX only)
//! let time_zone_local = TimeZone::local()?;
//! let _date_time = DateTime::now(time_zone_local.as_ref())?;
//! # Ok(())
//! # }
//! ```

#![warn(unreachable_pub)]

use std::num::ParseIntError;
use std::str::Utf8Error;
use std::time::SystemTimeError;
use std::{error, fmt, io};

mod datetime;
pub use datetime::{DateTime, UtcDateTime};

mod timezone;
pub use timezone::{TimeZone, TimeZoneRef};

mod parser;
mod rule;

/// Unified error type for everything in the crate
#[derive(Debug)]
pub enum Error {
    /// Date time error
    DateTime(&'static str),
    /// Local time type search error
    FindLocalTimeType(&'static str),
    /// Local time type error
    LocalTimeType(&'static str),
    /// Invalid slice for integer conversion
    InvalidSlice(&'static str),
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
    /// Unsupported Tzif file
    UnsupportedTzFile(&'static str),
    /// Unsupported TZ string
    UnsupportedTzString(&'static str),
    /// UTF-8 error
    Utf8(Utf8Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            DateTime(error) => write!(f, "invalid date time: {}", error),
            FindLocalTimeType(error) => error.fmt(f),
            LocalTimeType(error) => write!(f, "invalid local time type: {}", error),
            InvalidSlice(error) => error.fmt(f),
            InvalidTzString(error) => write!(f, "invalid TZ string: {}", error),
            InvalidTzFile(error) => error.fmt(f),
            Io(error) => error.fmt(f),
            OutOfRange(error) => error.fmt(f),
            ParseInt(error) => error.fmt(f),
            ProjectDateTime(error) => error.fmt(f),
            SystemTime(error) => error.fmt(f),
            TransitionRule(error) => write!(f, "invalid transition rule: {}", error),
            TimeZone(error) => write!(f, "invalid time zone: {}", error),
            UnsupportedTzFile(error) => error.fmt(f),
            UnsupportedTzString(error) => write!(f, "unsupported TZ string: {}", error),
            Utf8(error) => error.fmt(f),
        }
    }
}

impl error::Error for Error {}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Error::Io(error)
    }
}

impl From<ParseIntError> for Error {
    fn from(error: ParseIntError) -> Self {
        Error::ParseInt(error)
    }
}

impl From<SystemTimeError> for Error {
    fn from(error: SystemTimeError) -> Self {
        Error::SystemTime(error)
    }
}

impl From<Utf8Error> for Error {
    fn from(error: Utf8Error) -> Self {
        Error::Utf8(error)
    }
}

// MSRV: 1.38
#[inline]
fn rem_euclid(v: i64, rhs: i64) -> i64 {
    let r = v % rhs;
    if r < 0 {
        if rhs < 0 {
            r - rhs
        } else {
            r + rhs
        }
    } else {
        r
    }
}

/// MSRV 1.42
#[cfg(test)]
#[macro_export]
macro_rules! matches {
    ($expression:expr, $(|)? $( $pattern:pat )|+ $( if $guard: expr )? $(,)?) => {
        match $expression {
            $( $pattern )|+ $( if $guard )? => true,
            _ => false
        }
    }
}

/// Number of hours in one day
const HOURS_PER_DAY: i64 = 24;
/// Number of seconds in one hour
const SECONDS_PER_HOUR: i64 = 3600;
/// Number of seconds in one day
const SECONDS_PER_DAY: i64 = SECONDS_PER_HOUR * HOURS_PER_DAY;
/// Number of days in one week
const DAYS_PER_WEEK: i64 = 7;

/// Month days in a normal year
const DAY_IN_MONTHS_NORMAL_YEAR: [i64; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
/// Cumulated month days in a normal year
const CUMUL_DAY_IN_MONTHS_NORMAL_YEAR: [i64; 12] =
    [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];
