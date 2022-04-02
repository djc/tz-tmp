//! Types related to a time zone.

use std::fs::{self, File};
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::{fmt, str};

use super::{Error, DAYS_PER_WEEK, SECONDS_PER_DAY};

mod parser;
mod rule;
use rule::{AlternateTime, TransitionRule};

#[cfg(test)]
mod tests;

/// Time zone
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TimeZone {
    /// List of transitions
    transitions: Vec<Transition>,
    /// List of local time types (cannot be empty)
    local_time_types: Vec<LocalTimeType>,
    /// List of leap seconds
    leap_seconds: Vec<LeapSecond>,
    /// Extra transition rule applicable after the last transition
    extra_rule: Option<TransitionRule>,
}

impl TimeZone {
    /// Returns local time zone.
    ///
    /// This method in not supported on non-UNIX platforms, and returns the UTC time zone instead.
    ///
    pub fn local() -> Result<Self, Error> {
        #[cfg(not(unix))]
        let local_time_zone = Self::utc();

        #[cfg(unix)]
        let local_time_zone = Self::from_posix_tz("localtime")?;

        Ok(local_time_zone)
    }

    /// Construct a time zone from a POSIX TZ string, as described in [the POSIX documentation of the `TZ` environment variable](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html).
    pub fn from_posix_tz(tz_string: &str) -> Result<Self, Error> {
        if tz_string.is_empty() {
            return Err(Error::InvalidTzString("empty TZ string"));
        }

        if tz_string == "localtime" {
            return Self::from_tz_data(&fs::read("/etc/localtime")?);
        }

        let mut chars = tz_string.chars();
        if chars.next() == Some(':') {
            return Self::from_file(&mut find_tz_file(chars.as_str())?);
        }

        if let Ok(mut file) = find_tz_file(tz_string) {
            return Self::from_file(&mut file);
        }

        // TZ string extensions are not allowed
        let tz_string = tz_string.trim_matches(|c: char| c.is_ascii_whitespace());
        let rule = TransitionRule::from_tz_string(tz_string.as_bytes(), false)?;
        Self::new(
            vec![],
            match rule {
                TransitionRule::Fixed(local_time_type) => vec![local_time_type],
                TransitionRule::Alternate(AlternateTime { std, dst, .. }) => vec![std, dst],
            },
            vec![],
            Some(rule),
        )
    }

    /// Construct a time zone
    fn new(
        transitions: Vec<Transition>,
        local_time_types: Vec<LocalTimeType>,
        leap_seconds: Vec<LeapSecond>,
        extra_rule: Option<TransitionRule>,
    ) -> Result<Self, Error> {
        let new = Self { transitions, local_time_types, leap_seconds, extra_rule };
        new.as_ref().check_inputs()?;
        Ok(new)
    }

    /// Construct a time zone from the contents of a time zone file
    pub fn from_file(file: &mut File) -> Result<Self, Error> {
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)?;
        Self::from_tz_data(&bytes)
    }

    /// Construct a time zone from the contents of a time zone file
    ///
    /// Parse TZif data as described in [RFC 8536](https://datatracker.ietf.org/doc/html/rfc8536).
    pub fn from_tz_data(bytes: &[u8]) -> Result<Self, Error> {
        parser::parse(bytes)
    }

    /// Construct a time zone with the specified UTC offset in seconds
    pub fn fixed(ut_offset: i32) -> Result<Self, Error> {
        Ok(Self {
            transitions: Vec::new(),
            local_time_types: vec![LocalTimeType::with_ut_offset(ut_offset)?],
            leap_seconds: Vec::new(),
            extra_rule: None,
        })
    }

    /// Construct the time zone associated to UTC
    pub fn utc() -> Self {
        Self {
            transitions: Vec::new(),
            local_time_types: vec![LocalTimeType::utc()],
            leap_seconds: Vec::new(),
            extra_rule: None,
        }
    }

    /// Find the local time type associated to the time zone at the specified Unix time in seconds
    pub fn find_local_time_type(&self, unix_time: i64) -> Result<&LocalTimeType, Error> {
        self.as_ref().find_local_time_type(unix_time)
    }

    /// Returns a reference to the time zone
    pub fn as_ref(&self) -> TimeZoneRef {
        TimeZoneRef {
            transitions: &self.transitions,
            local_time_types: &self.local_time_types,
            leap_seconds: &self.leap_seconds,
            extra_rule: &self.extra_rule,
        }
    }
}

/// Reference to a time zone
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct TimeZoneRef<'a> {
    /// List of transitions
    transitions: &'a [Transition],
    /// List of local time types (cannot be empty)
    local_time_types: &'a [LocalTimeType],
    /// List of leap seconds
    leap_seconds: &'a [LeapSecond],
    /// Extra transition rule applicable after the last transition
    extra_rule: &'a Option<TransitionRule>,
}

impl<'a> TimeZoneRef<'a> {
    /// Construct the time zone reference associated to UTC
    pub const fn utc() -> Self {
        Self {
            transitions: &[],
            local_time_types: &[UTC_TYPE],
            leap_seconds: &[],
            extra_rule: &None,
        }
    }

    /// Returns list of transitions
    pub fn transitions(&self) -> &'a [Transition] {
        self.transitions
    }

    /// Returns list of local time types
    pub fn local_time_types(&self) -> &'a [LocalTimeType] {
        self.local_time_types
    }

    /// Returns list of leap seconds
    pub fn leap_seconds(&self) -> &'a [LeapSecond] {
        self.leap_seconds
    }

    /// Find the local time type associated to the time zone at the specified Unix time in seconds
    pub fn find_local_time_type(&self, unix_time: i64) -> Result<&'a LocalTimeType, Error> {
        let extra_rule = match self.transitions.last() {
            None => match self.extra_rule {
                Some(extra_rule) => extra_rule,
                None => return Ok(&self.local_time_types[0]),
            },
            Some(last_transition) => {
                let unix_leap_time = match self.unix_time_to_unix_leap_time(unix_time) {
                    Ok(unix_leap_time) => unix_leap_time,
                    Err(Error::OutOfRange(error)) => return Err(Error::FindLocalTimeType(error)),
                    Err(err) => return Err(err),
                };

                if unix_leap_time >= last_transition.unix_leap_time {
                    match self.extra_rule {
                        Some(extra_rule) => extra_rule,
                        None => {
                            return Err(Error::FindLocalTimeType(
                                "no local time type is available for the specified timestamp",
                            ))
                        }
                    }
                } else {
                    let index = match self
                        .transitions
                        .binary_search_by_key(&unix_leap_time, Transition::unix_leap_time)
                    {
                        Ok(x) => x + 1,
                        Err(x) => x,
                    };

                    let local_time_type_index = if index > 0 {
                        self.transitions[index - 1].local_time_type_index
                    } else {
                        0
                    };
                    return Ok(&self.local_time_types[local_time_type_index]);
                }
            }
        };

        match extra_rule.find_local_time_type(unix_time) {
            Ok(local_time_type) => Ok(local_time_type),
            Err(Error::OutOfRange(error)) => Err(Error::FindLocalTimeType(error)),
            err => err,
        }
    }

    /// Check time zone inputs
    fn check_inputs(&self) -> Result<(), Error> {
        // Check local time types
        let local_time_types_size = self.local_time_types.len();
        if local_time_types_size == 0 {
            return Err(Error::TimeZone("list of local time types must not be empty"));
        }

        // Check transitions
        let mut i_transition = 0;
        while i_transition < self.transitions.len() {
            if self.transitions[i_transition].local_time_type_index >= local_time_types_size {
                return Err(Error::TimeZone("invalid local time type index"));
            }

            if i_transition + 1 < self.transitions.len()
                && self.transitions[i_transition].unix_leap_time
                    >= self.transitions[i_transition + 1].unix_leap_time
            {
                return Err(Error::TimeZone("invalid transition"));
            }

            i_transition += 1;
        }

        // Check leap seconds
        if !(self.leap_seconds.is_empty()
            || self.leap_seconds[0].unix_leap_time >= 0
                && self.leap_seconds[0].correction.saturating_abs() == 1)
        {
            return Err(Error::TimeZone("invalid leap second"));
        }

        let min_interval = SECONDS_PER_28_DAYS - 1;

        let mut i_leap_second = 0;
        while i_leap_second < self.leap_seconds.len() {
            if i_leap_second + 1 < self.leap_seconds.len() {
                let x0 = &self.leap_seconds[i_leap_second];
                let x1 = &self.leap_seconds[i_leap_second + 1];

                let diff_unix_leap_time = x1.unix_leap_time.saturating_sub(x0.unix_leap_time);
                let abs_diff_correction =
                    x1.correction.saturating_sub(x0.correction).saturating_abs();

                if !(diff_unix_leap_time >= min_interval && abs_diff_correction == 1) {
                    return Err(Error::TimeZone("invalid leap second"));
                }
            }
            i_leap_second += 1;
        }

        // Check extra rule
        if let (Some(extra_rule), Some(last_transition)) =
            (&self.extra_rule, self.transitions.last())
        {
            let last_local_time_type =
                &self.local_time_types[last_transition.local_time_type_index];

            let unix_time = match self.unix_leap_time_to_unix_time(last_transition.unix_leap_time) {
                Ok(unix_time) => unix_time,
                Err(Error::OutOfRange(error)) => return Err(Error::TimeZone(error)),
                Err(err) => return Err(err),
            };

            let rule_local_time_type = match extra_rule.find_local_time_type(unix_time) {
                Ok(rule_local_time_type) => rule_local_time_type,
                Err(Error::OutOfRange(error)) => return Err(Error::TimeZone(error)),
                Err(err) => return Err(err),
            };

            let check = last_local_time_type.ut_offset == rule_local_time_type.ut_offset
                && last_local_time_type.is_dst == rule_local_time_type.is_dst
                && match (
                    &last_local_time_type.time_zone_designation,
                    &rule_local_time_type.time_zone_designation,
                ) {
                    (Some(x), Some(y)) => x.equal(y),
                    (None, None) => true,
                    _ => false,
                };

            if !check {
                return Err(Error::TimeZone(
                    "extra transition rule is inconsistent with the last transition",
                ));
            }
        }

        Ok(())
    }

    /// Convert Unix time to Unix leap time, from the list of leap seconds in a time zone
    const fn unix_time_to_unix_leap_time(&self, unix_time: i64) -> Result<i64, Error> {
        let mut unix_leap_time = unix_time;

        let mut i = 0;
        while i < self.leap_seconds.len() {
            let leap_second = &self.leap_seconds[i];

            if unix_leap_time < leap_second.unix_leap_time {
                break;
            }

            unix_leap_time = match unix_time.checked_add(leap_second.correction as i64) {
                Some(unix_leap_time) => unix_leap_time,
                None => return Err(Error::OutOfRange("out of range operation")),
            };

            i += 1;
        }

        Ok(unix_leap_time)
    }

    /// Convert Unix leap time to Unix time, from the list of leap seconds in a time zone
    fn unix_leap_time_to_unix_time(&self, unix_leap_time: i64) -> Result<i64, Error> {
        if unix_leap_time == i64::MIN {
            return Err(Error::OutOfRange("out of range operation"));
        }

        let index = match self
            .leap_seconds
            .binary_search_by_key(&(unix_leap_time - 1), LeapSecond::unix_leap_time)
        {
            Ok(x) => x + 1,
            Err(x) => x,
        };

        let correction = if index > 0 { self.leap_seconds[index - 1].correction } else { 0 };

        match unix_leap_time.checked_sub(correction as i64) {
            Some(unix_time) => Ok(unix_time),
            None => Err(Error::OutOfRange("out of range operation")),
        }
    }
}

/// Transition of a TZif file
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Transition {
    /// Unix leap time
    unix_leap_time: i64,
    /// Index specifying the local time type of the transition
    local_time_type_index: usize,
}

impl Transition {
    /// Construct a TZif file transition
    pub fn new(unix_leap_time: i64, local_time_type_index: usize) -> Self {
        Self { unix_leap_time, local_time_type_index }
    }

    /// Returns Unix leap time
    pub fn unix_leap_time(&self) -> i64 {
        self.unix_leap_time
    }

    /// Returns local time type index
    pub fn local_time_type_index(&self) -> usize {
        self.local_time_type_index
    }
}

/// Leap second of a TZif file
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct LeapSecond {
    /// Unix leap time
    unix_leap_time: i64,
    /// Leap second correction
    correction: i32,
}

impl LeapSecond {
    /// Construct a TZif file leap second
    pub fn new(unix_leap_time: i64, correction: i32) -> Self {
        Self { unix_leap_time, correction }
    }

    /// Returns Unix leap time
    pub fn unix_leap_time(&self) -> i64 {
        self.unix_leap_time
    }

    /// Returns leap second correction
    pub fn correction(&self) -> i32 {
        self.correction
    }
}

/// ASCII-encoded fixed-capacity string, used for storing time zone designations
#[derive(Copy, Clone, Eq, PartialEq)]
struct TzAsciiStr {
    /// Length-prefixed string buffer
    bytes: [u8; 8],
}

impl TzAsciiStr {
    /// Construct a time zone designation string
    const fn new(input: &[u8]) -> Result<Self, Error> {
        let len = input.len();

        if !(3 <= len && len <= 7) {
            return Err(Error::LocalTimeType(
                "time zone designation must have between 3 and 7 characters",
            ));
        }

        let mut bytes = [0; 8];
        bytes[0] = input.len() as u8;

        let mut i = 0;
        while i < len {
            let b = input[i];

            if !matches!(b, b'0'..=b'9' | b'A'..=b'Z' | b'a'..=b'z' | b'+' | b'-') {
                return Err(Error::LocalTimeType("invalid characters in time zone designation"));
            }

            bytes[i + 1] = b;

            i += 1;
        }

        Ok(Self { bytes })
    }

    /// Returns time zone designation as a byte slice
    const fn as_bytes(&self) -> &[u8] {
        match &self.bytes {
            [3, head @ .., _, _, _, _] => head,
            [4, head @ .., _, _, _] => head,
            [5, head @ .., _, _] => head,
            [6, head @ .., _] => head,
            [7, head @ ..] => head,
            _ => unreachable!(),
        }
    }

    /// Returns time zone designation as a string
    const fn as_str(&self) -> &str {
        // SAFETY: ASCII is valid UTF-8
        unsafe { str::from_utf8_unchecked(self.as_bytes()) }
    }

    /// Check if two time zone designations are equal
    const fn equal(&self, other: &Self) -> bool {
        u64::from_ne_bytes(self.bytes) == u64::from_ne_bytes(other.bytes)
    }
}

impl fmt::Debug for TzAsciiStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

/// Local time type associated to a time zone
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct LocalTimeType {
    /// Offset from UTC in seconds
    ut_offset: i32,
    /// Daylight Saving Time indicator
    is_dst: bool,
    /// Time zone designation
    time_zone_designation: Option<TzAsciiStr>,
}

impl LocalTimeType {
    /// Construct a local time type
    pub fn new(
        ut_offset: i32,
        is_dst: bool,
        time_zone_designation: Option<&[u8]>,
    ) -> Result<Self, Error> {
        if ut_offset == i32::MIN {
            return Err(Error::LocalTimeType("invalid UTC offset"));
        }

        let time_zone_designation = match time_zone_designation {
            None => None,
            Some(time_zone_designation) => match TzAsciiStr::new(time_zone_designation) {
                Err(error) => return Err(error),
                Ok(time_zone_designation) => Some(time_zone_designation),
            },
        };

        Ok(Self { ut_offset, is_dst, time_zone_designation })
    }

    /// Construct the local time type associated to UTC
    pub const fn utc() -> Self {
        Self { ut_offset: 0, is_dst: false, time_zone_designation: None }
    }

    /// Construct a local time type with the specified UTC offset in seconds
    pub fn with_ut_offset(ut_offset: i32) -> Result<Self, Error> {
        if ut_offset == i32::MIN {
            return Err(Error::LocalTimeType("invalid UTC offset"));
        }

        Ok(Self { ut_offset, is_dst: false, time_zone_designation: None })
    }

    /// Returns offset from UTC in seconds
    pub fn ut_offset(&self) -> i32 {
        self.ut_offset
    }

    /// Returns daylight saving time indicator
    pub fn is_dst(&self) -> bool {
        self.is_dst
    }

    /// Returns time zone designation
    pub fn time_zone_designation(&self) -> &str {
        match &self.time_zone_designation {
            Some(s) => s.as_str(),
            None => "",
        }
    }
}

/// Open the TZif file corresponding to a TZ string
fn find_tz_file(path: impl AsRef<Path>) -> Result<File, Error> {
    // Don't check system timezone directories on non-UNIX platforms
    #[cfg(not(unix))]
    return Ok(File::open(path)?);

    #[cfg(unix)]
    {
        let path = path.as_ref();
        if path.is_absolute() {
            return Ok(File::open(path)?);
        }

        for folder in &ZONE_INFO_DIRECTORIES {
            if let Ok(file) = File::open(PathBuf::from(folder).join(path)) {
                return Ok(file);
            }
        }

        Err(Error::Io(io::ErrorKind::NotFound.into()))
    }
}

// Possible system timezone directories
#[cfg(unix)]
const ZONE_INFO_DIRECTORIES: [&str; 3] =
    ["/usr/share/zoneinfo", "/share/zoneinfo", "/etc/zoneinfo"];

/// Number of seconds in one week
const SECONDS_PER_WEEK: i64 = SECONDS_PER_DAY * DAYS_PER_WEEK;
/// Number of seconds in 28 days
const SECONDS_PER_28_DAYS: i64 = SECONDS_PER_DAY * 28;

const UTC_TYPE: LocalTimeType = LocalTimeType::utc();
