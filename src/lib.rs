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
//! # fn main() -> Result<(), tz::TzError> {
//! use tz::TimeZone;
//!
//! // 2000-01-01T00:00:00Z
//! let unix_time = 946684800;
//!
//! // Get UTC time zone
//! let time_zone_utc = TimeZone::utc();
//! assert_eq!(time_zone_utc.find_local_time_type(unix_time)?.ut_offset(), 0);
//!
//! // Get fixed time zone at GMT-1
//! let time_zone_fixed = TimeZone::fixed(-3600)?;
//! assert_eq!(time_zone_fixed.find_local_time_type(unix_time)?.ut_offset(), -3600);
//!
//! // Get local time zone (UNIX only)
//! let time_zone_local = TimeZone::local()?;
//! // Get the current local time type
//! let _current_local_time_type = time_zone_local.find_current_local_time_type()?;
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
//! # fn main() -> Result<(), tz::TzError> {
//! use tz::{DateTime, TimeZone, UtcDateTime};
//!
//! // Get the current UTC date time
//! let _current_utc_date_time = UtcDateTime::now()?;
//!
//! // Create a new UTC date time (2000-01-01T00:00:00.123456789Z)
//! let utc_date_time = UtcDateTime::new(2000, 1, 1, 0, 0, 0, 123_456_789)?;
//! assert_eq!(utc_date_time.year(), 2000);
//! assert_eq!(utc_date_time.month(), 1);
//! assert_eq!(utc_date_time.month_day(), 1);
//! assert_eq!(utc_date_time.hour(), 0);
//! assert_eq!(utc_date_time.minute(), 0);
//! assert_eq!(utc_date_time.second(), 0);
//! assert_eq!(utc_date_time.week_day(), 6);
//! assert_eq!(utc_date_time.year_day(), 0);
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
//! assert_eq!(date_time.week_day(), 5);
//! assert_eq!(date_time.year_day(), 364);
//! assert_eq!(date_time.local_time_type().ut_offset(), -3600);
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
//! assert_eq!(other_date_time.week_day(), 6);
//! assert_eq!(other_date_time.year_day(), 0);
//! assert_eq!(other_date_time.local_time_type().ut_offset(), 3600);
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

use std::convert::TryInto;
use std::io::{Error, ErrorKind};
use std::num::ParseIntError;
use std::str::{self, FromStr};

use crate::error::{TzFileError, TzStringError};

mod datetime;
pub use datetime::{DateTime, UtcDateTime};

mod error;
pub use error::TzError;

mod timezone;
pub use timezone::{TimeZone, TimeZoneRef};

/// A `Cursor` contains a slice of a buffer and a read count.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Cursor<'a> {
    /// Slice representing the remaining data to be read
    remaining: &'a [u8],
    /// Number of already read bytes
    read_count: usize,
}

impl<'a> Cursor<'a> {
    /// Construct a new `Cursor` from remaining data
    pub(crate) fn new(remaining: &'a [u8]) -> Self {
        Self { remaining, read_count: 0 }
    }

    pub(crate) fn peek(&self) -> Option<&u8> {
        self.remaining().get(0)
    }

    /// Returns remaining data
    pub(crate) fn remaining(&self) -> &'a [u8] {
        self.remaining
    }

    /// Returns `true` if data is remaining
    pub(crate) fn is_empty(&self) -> bool {
        self.remaining.is_empty()
    }

    pub(crate) fn read_be_u32(&mut self) -> Result<u32, TzFileError> {
        Ok(u32::from_be_bytes(self.read_exact(4)?.try_into()?))
    }

    /// Read exactly `count` bytes, reducing remaining data and incrementing read count
    pub(crate) fn read_exact(&mut self, count: usize) -> Result<&'a [u8], Error> {
        match (self.remaining.get(..count), self.remaining.get(count..)) {
            (Some(result), Some(remaining)) => {
                self.remaining = remaining;
                self.read_count += count;
                Ok(result)
            }
            _ => Err(Error::from(ErrorKind::UnexpectedEof)),
        }
    }

    /// Read bytes and compare them to the provided tag
    pub(crate) fn read_tag(&mut self, tag: &[u8]) -> Result<(), Error> {
        if self.read_exact(tag.len())? == tag {
            Ok(())
        } else {
            Err(Error::from(ErrorKind::InvalidData))
        }
    }

    /// Read bytes if the remaining data is prefixed by the provided tag
    pub(crate) fn read_optional_tag(&mut self, tag: &[u8]) -> Result<bool, Error> {
        if self.remaining.starts_with(tag) {
            self.read_exact(tag.len())?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Read bytes as long as the provided predicate is true
    pub(crate) fn read_while<F: Fn(&u8) -> bool>(&mut self, f: F) -> Result<&'a [u8], Error> {
        match self.remaining.iter().position(|x| !f(x)) {
            None => self.read_exact(self.remaining.len()),
            Some(position) => self.read_exact(position),
        }
    }

    // Parse an integer out of the ASCII digits
    pub(crate) fn read_int<T: FromStr<Err = ParseIntError>>(&mut self) -> Result<T, TzStringError> {
        let bytes = self.read_while(u8::is_ascii_digit)?;
        Ok(str::from_utf8(bytes)?.parse()?)
    }

    /// Read bytes until the provided predicate is true
    pub(crate) fn read_until<F: Fn(&u8) -> bool>(&mut self, f: F) -> Result<&'a [u8], Error> {
        match self.remaining.iter().position(f) {
            None => self.read_exact(self.remaining.len()),
            Some(position) => self.read_exact(position),
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
