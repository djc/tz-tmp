//! Types related to a time zone.

use std::cmp::Ordering;
use std::convert::TryInto;
use std::fs::{self, File};
use std::io::{self, Read};
use std::time::SystemTime;
use std::{fmt, iter, str};

use super::{
    Cursor, CUMUL_DAY_IN_MONTHS_NORMAL_YEAR, DAYS_PER_WEEK, DAY_IN_MONTHS_NORMAL_YEAR,
    SECONDS_PER_DAY,
};
use crate::datetime::{days_since_unix_epoch, is_leap_year, UtcDateTime};
use crate::error::{
    FindLocalTimeTypeError, LocalTimeTypeError, OutOfRangeError, TimeZoneError,
    TransitionRuleError, TzError, TzFileError, TzStringError,
};

#[cfg(test)]
mod tests;

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
    const fn new(input: &[u8]) -> Result<Self, LocalTimeTypeError> {
        let len = input.len();

        if !(3 <= len && len <= 7) {
            return Err(LocalTimeTypeError(
                "time zone designation must have between 3 and 7 characters",
            ));
        }

        let mut bytes = [0; 8];
        bytes[0] = input.len() as u8;

        let mut i = 0;
        while i < len {
            let b = input[i];

            if !matches!(b, b'0'..=b'9' | b'A'..=b'Z' | b'a'..=b'z' | b'+' | b'-') {
                return Err(LocalTimeTypeError("invalid characters in time zone designation"));
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
    ) -> Result<Self, LocalTimeTypeError> {
        if ut_offset == i32::MIN {
            return Err(LocalTimeTypeError("invalid UTC offset"));
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
    pub fn with_ut_offset(ut_offset: i32) -> Result<Self, LocalTimeTypeError> {
        if ut_offset == i32::MIN {
            return Err(LocalTimeTypeError("invalid UTC offset"));
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

/// Julian day in `[1, 365]`, without taking occasional Feb 29 into account, which is not referenceable
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Julian1WithoutLeap(u16);

impl Julian1WithoutLeap {
    /// Construct a transition rule day represented by a Julian day in `[1, 365]`, without taking occasional Feb 29 into account, which is not referenceable
    pub fn new(julian_day_1: u16) -> Result<Self, TransitionRuleError> {
        if !(1 <= julian_day_1 && julian_day_1 <= 365) {
            return Err(TransitionRuleError("invalid rule day julian day"));
        }

        Ok(Self(julian_day_1))
    }

    /// Returns inner value
    pub fn get(&self) -> u16 {
        self.0
    }
}

/// Zero-based Julian day in `[0, 365]`, taking occasional Feb 29 into account
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Julian0WithLeap(u16);

impl Julian0WithLeap {
    /// Construct a transition rule day represented by a zero-based Julian day in `[0, 365]`, taking occasional Feb 29 into account
    pub fn new(julian_day_0: u16) -> Result<Self, TransitionRuleError> {
        if julian_day_0 > 365 {
            return Err(TransitionRuleError("invalid rule day julian day"));
        }

        Ok(Self(julian_day_0))
    }

    /// Returns inner value
    pub fn get(&self) -> u16 {
        self.0
    }
}

/// Day represented by a month, a month week and a week day
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct MonthWeekDay {
    /// Month in `[1, 12]`
    month: u8,
    /// Week of the month in `[1, 5]`, with `5` representing the last week of the month
    week: u8,
    /// Day of the week in `[0, 6]` from Sunday
    week_day: u8,
}

impl MonthWeekDay {
    /// Construct a transition rule day represented by a month, a month week and a week day
    pub fn new(month: u8, week: u8, week_day: u8) -> Result<Self, TransitionRuleError> {
        if !(1 <= month && month <= 12) {
            return Err(TransitionRuleError("invalid rule day month"));
        }

        if !(1 <= week && week <= 5) {
            return Err(TransitionRuleError("invalid rule day week"));
        }

        if week_day > 6 {
            return Err(TransitionRuleError("invalid rule day week day"));
        }

        Ok(Self { month, week, week_day })
    }

    /// Returns month in `[1, 12]`
    pub fn month(&self) -> u8 {
        self.month
    }

    /// Returns week of the month in `[1, 5]`, with `5` representing the last week of the month
    pub fn week(&self) -> u8 {
        self.week
    }

    /// Returns day of the week in `[0, 6]` from Sunday
    pub fn week_day(&self) -> u8 {
        self.week_day
    }
}

/// Transition rule day
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum RuleDay {
    /// Julian day in `[1, 365]`, without taking occasional Feb 29 into account, which is not referenceable
    Julian1WithoutLeap(Julian1WithoutLeap),
    /// Zero-based Julian day in `[0, 365]`, taking occasional Feb 29 into account
    Julian0WithLeap(Julian0WithLeap),
    /// Day represented by a month, a month week and a week day
    MonthWeekDay(MonthWeekDay),
}

impl RuleDay {
    /// Get the transition date for the provided year
    ///
    /// ## Outputs
    ///
    /// * `month`: Month in `[1, 12]`
    /// * `month_day`: Day of the month in `[1, 31]`
    fn transition_date(&self, year: i32) -> (usize, i64) {
        match *self {
            Self::Julian1WithoutLeap(Julian1WithoutLeap(year_day)) => {
                let year_day = year_day as i64;

                let month = match CUMUL_DAY_IN_MONTHS_NORMAL_YEAR.binary_search(&(year_day - 1)) {
                    Ok(x) => x + 1,
                    Err(x) => x,
                };

                let month_day = year_day - CUMUL_DAY_IN_MONTHS_NORMAL_YEAR[month - 1];

                (month, month_day)
            }
            Self::Julian0WithLeap(Julian0WithLeap(year_day)) => {
                let leap = is_leap_year(year) as i64;

                let cumul_day_in_months = [
                    0,
                    31,
                    59 + leap,
                    90 + leap,
                    120 + leap,
                    151 + leap,
                    181 + leap,
                    212 + leap,
                    243 + leap,
                    273 + leap,
                    304 + leap,
                    334 + leap,
                ];

                let year_day = year_day as i64;

                let month = match cumul_day_in_months.binary_search(&year_day) {
                    Ok(x) => x + 1,
                    Err(x) => x,
                };

                let month_day = 1 + year_day - cumul_day_in_months[month - 1];

                (month, month_day)
            }
            Self::MonthWeekDay(MonthWeekDay { month: rule_month, week, week_day }) => {
                let leap = is_leap_year(year) as i64;

                let month = rule_month as usize;

                let mut day_in_month = DAY_IN_MONTHS_NORMAL_YEAR[month - 1];
                if month == 2 {
                    day_in_month += leap;
                }

                let week_day_of_first_month_day =
                    (4 + days_since_unix_epoch(year, month, 1)).rem_euclid(DAYS_PER_WEEK);
                let first_week_day_occurence_in_month =
                    1 + (week_day as i64 - week_day_of_first_month_day).rem_euclid(DAYS_PER_WEEK);

                let mut month_day =
                    first_week_day_occurence_in_month + (week as i64 - 1) * DAYS_PER_WEEK;
                if month_day > day_in_month {
                    month_day -= DAYS_PER_WEEK
                }

                (month, month_day)
            }
        }
    }

    /// Returns the UTC Unix time in seconds associated to the transition date for the provided year
    fn unix_time(&self, year: i32, day_time_in_utc: i64) -> i64 {
        let (month, month_day) = self.transition_date(year);
        days_since_unix_epoch(year, month, month_day) * SECONDS_PER_DAY + day_time_in_utc
    }
}

impl From<Julian0WithLeap> for RuleDay {
    fn from(inner: Julian0WithLeap) -> Self {
        Self::Julian0WithLeap(inner)
    }
}

impl From<Julian1WithoutLeap> for RuleDay {
    fn from(inner: Julian1WithoutLeap) -> Self {
        Self::Julian1WithoutLeap(inner)
    }
}

impl From<MonthWeekDay> for RuleDay {
    fn from(inner: MonthWeekDay) -> Self {
        Self::MonthWeekDay(inner)
    }
}

/// Transition rule representing alternate local time types
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct AlternateTime {
    /// Local time type for standard time
    std: LocalTimeType,
    /// Local time type for Daylight Saving Time
    dst: LocalTimeType,
    /// Start day of Daylight Saving Time
    dst_start: RuleDay,
    /// Local start day time of Daylight Saving Time, in seconds
    dst_start_time: i32,
    /// End day of Daylight Saving Time
    dst_end: RuleDay,
    /// Local end day time of Daylight Saving Time, in seconds
    dst_end_time: i32,
}

impl AlternateTime {
    /// Construct a transition rule representing alternate local time types
    pub fn new(
        std: LocalTimeType,
        dst: LocalTimeType,
        dst_start: RuleDay,
        dst_start_time: i32,
        dst_end: RuleDay,
        dst_end_time: i32,
    ) -> Result<Self, TransitionRuleError> {
        // Overflow is not possible
        if !((dst_start_time as i64).abs() < SECONDS_PER_WEEK
            && (dst_end_time as i64).abs() < SECONDS_PER_WEEK)
        {
            return Err(TransitionRuleError("invalid DST start or end time"));
        }

        Ok(Self { std, dst, dst_start, dst_start_time, dst_end, dst_end_time })
    }

    /// Find the local time type associated to the alternate transition rule at the specified Unix time in seconds
    fn find_local_time_type(&self, unix_time: i64) -> Result<&LocalTimeType, OutOfRangeError> {
        // Overflow is not possible
        let dst_start_time_in_utc = self.dst_start_time as i64 - self.std.ut_offset as i64;
        let dst_end_time_in_utc = self.dst_end_time as i64 - self.dst.ut_offset as i64;

        let current_year = match UtcDateTime::from_timespec(unix_time, 0) {
            Ok(utc_date_time) => utc_date_time.year(),
            Err(error) => return Err(error),
        };

        // Check if the current year is valid for the following computations
        if !(i32::MIN + 2 <= current_year && current_year <= i32::MAX - 2) {
            return Err(OutOfRangeError("out of range date time"));
        }

        let current_year_dst_start_unix_time =
            self.dst_start.unix_time(current_year, dst_start_time_in_utc);
        let current_year_dst_end_unix_time =
            self.dst_end.unix_time(current_year, dst_end_time_in_utc);

        // Check DST start/end Unix times for previous/current/next years to support for transition day times outside of [0h, 24h] range
        let is_dst =
            match Ord::cmp(&current_year_dst_start_unix_time, &current_year_dst_end_unix_time) {
                Ordering::Less | Ordering::Equal => {
                    if unix_time < current_year_dst_start_unix_time {
                        let previous_year_dst_end_unix_time =
                            self.dst_end.unix_time(current_year - 1, dst_end_time_in_utc);
                        if unix_time < previous_year_dst_end_unix_time {
                            let previous_year_dst_start_unix_time =
                                self.dst_start.unix_time(current_year - 1, dst_start_time_in_utc);
                            previous_year_dst_start_unix_time <= unix_time
                        } else {
                            false
                        }
                    } else if unix_time < current_year_dst_end_unix_time {
                        true
                    } else {
                        let next_year_dst_start_unix_time =
                            self.dst_start.unix_time(current_year + 1, dst_start_time_in_utc);
                        if next_year_dst_start_unix_time <= unix_time {
                            let next_year_dst_end_unix_time =
                                self.dst_end.unix_time(current_year + 1, dst_end_time_in_utc);
                            unix_time < next_year_dst_end_unix_time
                        } else {
                            false
                        }
                    }
                }
                Ordering::Greater => {
                    if unix_time < current_year_dst_end_unix_time {
                        let previous_year_dst_start_unix_time =
                            self.dst_start.unix_time(current_year - 1, dst_start_time_in_utc);
                        if unix_time < previous_year_dst_start_unix_time {
                            let previous_year_dst_end_unix_time =
                                self.dst_end.unix_time(current_year - 1, dst_end_time_in_utc);
                            unix_time < previous_year_dst_end_unix_time
                        } else {
                            true
                        }
                    } else if unix_time < current_year_dst_start_unix_time {
                        false
                    } else {
                        let next_year_dst_end_unix_time =
                            self.dst_end.unix_time(current_year + 1, dst_end_time_in_utc);
                        if next_year_dst_end_unix_time <= unix_time {
                            let next_year_dst_start_unix_time =
                                self.dst_start.unix_time(current_year + 1, dst_start_time_in_utc);
                            next_year_dst_start_unix_time <= unix_time
                        } else {
                            true
                        }
                    }
                }
            };

        if is_dst {
            Ok(&self.dst)
        } else {
            Ok(&self.std)
        }
    }
}

/// Parse time zone designation
fn parse_time_zone_designation<'a>(cursor: &mut Cursor<'a>) -> Result<&'a [u8], TzStringError> {
    match cursor.peek() {
        Some(b'<') => {}
        _ => return Ok(cursor.read_while(u8::is_ascii_alphabetic)?),
    }

    cursor.read_exact(1)?;
    let unquoted = cursor.read_until(|&x| x == b'>')?;
    cursor.read_exact(1)?;
    Ok(unquoted)
}

/// Parse hours, minutes and seconds
fn parse_hhmmss(cursor: &mut Cursor) -> Result<(i32, i32, i32), TzStringError> {
    let hour = cursor.read_int()?;

    let mut minute = 0;
    let mut second = 0;

    if cursor.read_optional_tag(b":")? {
        minute = cursor.read_int()?;

        if cursor.read_optional_tag(b":")? {
            second = cursor.read_int()?;
        }
    }

    Ok((hour, minute, second))
}

/// Parse signed hours, minutes and seconds
fn parse_signed_hhmmss(cursor: &mut Cursor) -> Result<(i32, i32, i32, i32), TzStringError> {
    let mut sign = 1;
    if let Some(&c @ b'+') | Some(&c @ b'-') = cursor.peek() {
        cursor.read_exact(1)?;
        if c == b'-' {
            sign = -1;
        }
    }

    let (hour, minute, second) = parse_hhmmss(cursor)?;
    Ok((sign, hour, minute, second))
}

/// Parse time zone offset
fn parse_offset(cursor: &mut Cursor) -> Result<i32, TzStringError> {
    let (sign, hour, minute, second) = parse_signed_hhmmss(cursor)?;

    if !(0..=24).contains(&hour) {
        return Err(TzStringError::InvalidTzString("invalid offset hour"));
    }
    if !(0..=59).contains(&minute) {
        return Err(TzStringError::InvalidTzString("invalid offset minute"));
    }
    if !(0..=59).contains(&second) {
        return Err(TzStringError::InvalidTzString("invalid offset second"));
    }

    Ok(sign * (hour * 3600 + minute * 60 + second))
}

/// Parse transition rule time
fn parse_rule_time(cursor: &mut Cursor) -> Result<i32, TzStringError> {
    let (hour, minute, second) = parse_hhmmss(cursor)?;

    if !(0..=24).contains(&hour) {
        return Err(TzStringError::InvalidTzString("invalid day time hour"));
    }
    if !(0..=59).contains(&minute) {
        return Err(TzStringError::InvalidTzString("invalid day time minute"));
    }
    if !(0..=59).contains(&second) {
        return Err(TzStringError::InvalidTzString("invalid day time second"));
    }

    Ok(hour * 3600 + minute * 60 + second)
}

/// Parse transition rule time with TZ string extensions
fn parse_rule_time_extended(cursor: &mut Cursor) -> Result<i32, TzStringError> {
    let (sign, hour, minute, second) = parse_signed_hhmmss(cursor)?;

    if !(-167..=167).contains(&hour) {
        return Err(TzStringError::InvalidTzString("invalid day time hour"));
    }
    if !(0..=59).contains(&minute) {
        return Err(TzStringError::InvalidTzString("invalid day time minute"));
    }
    if !(0..=59).contains(&second) {
        return Err(TzStringError::InvalidTzString("invalid day time second"));
    }

    Ok(sign * (hour * 3600 + minute * 60 + second))
}

/// Parse transition rule
fn parse_rule_block(
    cursor: &mut Cursor,
    use_string_extensions: bool,
) -> Result<(RuleDay, i32), TzError> {
    let date = match cursor.peek() {
        Some(b'M') => {
            cursor.read_exact(1)?;
            let month = cursor.read_int()?;
            cursor.read_tag(b".")?;
            let week = cursor.read_int()?;
            cursor.read_tag(b".")?;
            let week_day = cursor.read_int()?;
            MonthWeekDay::new(month, week, week_day)?.into()
        }
        Some(b'J') => {
            cursor.read_exact(1)?;
            Julian1WithoutLeap::new(cursor.read_int()?)?.into()
        }
        _ => Julian0WithLeap::new(cursor.read_int()?)?.into(),
    };

    Ok((
        date,
        match (cursor.read_optional_tag(b"/")?, use_string_extensions) {
            (false, _) => 2 * 3600,
            (true, true) => parse_rule_time_extended(cursor)?,
            (true, false) => parse_rule_time(cursor)?,
        },
    ))
}

/// Transition rule
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TransitionRule {
    /// Fixed local time type
    Fixed(LocalTimeType),
    /// Alternate local time types
    Alternate(AlternateTime),
}

impl TransitionRule {
    /// Parse a POSIX TZ string containing a time zone description, as described in [the POSIX documentation of the `TZ` environment variable](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html).
    ///
    /// TZ string extensions from [RFC 8536](https://datatracker.ietf.org/doc/html/rfc8536#section-3.3.1) may be used.
    ///
    fn from_tz_string(tz_string: &[u8], use_string_extensions: bool) -> Result<Self, TzError> {
        let mut cursor = Cursor::new(tz_string);

        let std_time_zone = Some(parse_time_zone_designation(&mut cursor)?);
        let std_offset = parse_offset(&mut cursor)?;

        if cursor.is_empty() {
            return Ok(LocalTimeType::new(-std_offset, false, std_time_zone)?.into());
        }

        let dst_time_zone = Some(parse_time_zone_designation(&mut cursor)?);

        let dst_offset = match cursor.peek() {
            Some(&b',') => std_offset - 3600,
            Some(_) => parse_offset(&mut cursor)?,
            None => {
                return Err(TzStringError::UnsupportedTzString(
                    "DST start and end rules must be provided",
                )
                .into())
            }
        };

        if cursor.is_empty() {
            return Err(TzStringError::UnsupportedTzString(
                "DST start and end rules must be provided",
            )
            .into());
        }

        cursor.read_tag(b",")?;
        let (dst_start, dst_start_time) = parse_rule_block(&mut cursor, use_string_extensions)?;

        cursor.read_tag(b",")?;
        let (dst_end, dst_end_time) = parse_rule_block(&mut cursor, use_string_extensions)?;

        if !cursor.is_empty() {
            return Err(
                TzStringError::InvalidTzString("remaining data after parsing TZ string").into()
            );
        }

        Ok(AlternateTime::new(
            LocalTimeType::new(-std_offset, false, std_time_zone)?,
            LocalTimeType::new(-dst_offset, true, dst_time_zone)?,
            dst_start,
            dst_start_time,
            dst_end,
            dst_end_time,
        )?
        .into())
    }

    /// Find the local time type associated to the transition rule at the specified Unix time in seconds
    fn find_local_time_type(&self, unix_time: i64) -> Result<&LocalTimeType, OutOfRangeError> {
        match self {
            Self::Fixed(local_time_type) => Ok(local_time_type),
            Self::Alternate(alternate_time) => alternate_time.find_local_time_type(unix_time),
        }
    }
}

impl From<LocalTimeType> for TransitionRule {
    fn from(inner: LocalTimeType) -> Self {
        Self::Fixed(inner)
    }
}

impl From<AlternateTime> for TransitionRule {
    fn from(inner: AlternateTime) -> Self {
        Self::Alternate(inner)
    }
}

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
    /// Construct a time zone reference
    pub fn new(
        transitions: &'a [Transition],
        local_time_types: &'a [LocalTimeType],
        leap_seconds: &'a [LeapSecond],
        extra_rule: &'a Option<TransitionRule>,
    ) -> Result<Self, TimeZoneError> {
        let time_zone_ref =
            Self::new_unchecked(transitions, local_time_types, leap_seconds, extra_rule);

        if let Err(error) = time_zone_ref.check_inputs() {
            return Err(error);
        }

        Ok(time_zone_ref)
    }

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

    /// Returns extra transition rule applicable after the last transition
    pub fn extra_rule(&self) -> &'a Option<TransitionRule> {
        self.extra_rule
    }

    /// Find the local time type associated to the time zone at the specified Unix time in seconds
    pub fn find_local_time_type(
        &self,
        unix_time: i64,
    ) -> Result<&'a LocalTimeType, FindLocalTimeTypeError> {
        let extra_rule = match self.transitions.last() {
            None => match self.extra_rule {
                Some(extra_rule) => extra_rule,
                None => return Ok(&self.local_time_types[0]),
            },
            Some(last_transition) => {
                let unix_leap_time = match self.unix_time_to_unix_leap_time(unix_time) {
                    Ok(unix_leap_time) => unix_leap_time,
                    Err(OutOfRangeError(error)) => return Err(FindLocalTimeTypeError(error)),
                };

                if unix_leap_time >= last_transition.unix_leap_time {
                    match self.extra_rule {
                        Some(extra_rule) => extra_rule,
                        None => {
                            return Err(FindLocalTimeTypeError(
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
            Err(OutOfRangeError(error)) => Err(FindLocalTimeTypeError(error)),
        }
    }

    /// Construct a reference to a time zone
    const fn new_unchecked(
        transitions: &'a [Transition],
        local_time_types: &'a [LocalTimeType],
        leap_seconds: &'a [LeapSecond],
        extra_rule: &'a Option<TransitionRule>,
    ) -> Self {
        Self { transitions, local_time_types, leap_seconds, extra_rule }
    }

    /// Check time zone inputs
    fn check_inputs(&self) -> Result<(), TimeZoneError> {
        // Check local time types
        let local_time_types_size = self.local_time_types.len();
        if local_time_types_size == 0 {
            return Err(TimeZoneError("list of local time types must not be empty"));
        }

        // Check transitions
        let mut i_transition = 0;
        while i_transition < self.transitions.len() {
            if self.transitions[i_transition].local_time_type_index >= local_time_types_size {
                return Err(TimeZoneError("invalid local time type index"));
            }

            if i_transition + 1 < self.transitions.len()
                && self.transitions[i_transition].unix_leap_time
                    >= self.transitions[i_transition + 1].unix_leap_time
            {
                return Err(TimeZoneError("invalid transition"));
            }

            i_transition += 1;
        }

        // Check leap seconds
        if !(self.leap_seconds.is_empty()
            || self.leap_seconds[0].unix_leap_time >= 0
                && self.leap_seconds[0].correction.saturating_abs() == 1)
        {
            return Err(TimeZoneError("invalid leap second"));
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
                    return Err(TimeZoneError("invalid leap second"));
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
                Err(OutOfRangeError(error)) => return Err(TimeZoneError(error)),
            };

            let rule_local_time_type = match extra_rule.find_local_time_type(unix_time) {
                Ok(rule_local_time_type) => rule_local_time_type,
                Err(OutOfRangeError(error)) => return Err(TimeZoneError(error)),
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
                return Err(TimeZoneError(
                    "extra transition rule is inconsistent with the last transition",
                ));
            }
        }

        Ok(())
    }

    /// Convert Unix time to Unix leap time, from the list of leap seconds in a time zone
    const fn unix_time_to_unix_leap_time(&self, unix_time: i64) -> Result<i64, OutOfRangeError> {
        let mut unix_leap_time = unix_time;

        let mut i = 0;
        while i < self.leap_seconds.len() {
            let leap_second = &self.leap_seconds[i];

            if unix_leap_time < leap_second.unix_leap_time {
                break;
            }

            unix_leap_time = match unix_time.checked_add(leap_second.correction as i64) {
                Some(unix_leap_time) => unix_leap_time,
                None => return Err(OutOfRangeError("out of range operation")),
            };

            i += 1;
        }

        Ok(unix_leap_time)
    }

    /// Convert Unix leap time to Unix time, from the list of leap seconds in a time zone
    fn unix_leap_time_to_unix_time(&self, unix_leap_time: i64) -> Result<i64, OutOfRangeError> {
        if unix_leap_time == i64::MIN {
            return Err(OutOfRangeError("out of range operation"));
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
            None => Err(OutOfRangeError("out of range operation")),
        }
    }
}

impl TimeZone {
    /// Returns local time zone.
    ///
    /// This method in not supported on non-UNIX platforms, and returns the UTC time zone instead.
    ///
    pub fn local() -> Result<Self, TzError> {
        #[cfg(not(unix))]
        let local_time_zone = Self::utc();

        #[cfg(unix)]
        let local_time_zone = Self::from_posix_tz("localtime")?;

        Ok(local_time_zone)
    }

    /// Construct a time zone from a POSIX TZ string, as described in [the POSIX documentation of the `TZ` environment variable](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html).
    pub fn from_posix_tz(tz_string: &str) -> Result<Self, TzError> {
        if tz_string.is_empty() {
            return Err(TzError::TzStringError(TzStringError::InvalidTzString("empty TZ string")));
        }

        if tz_string == "localtime" {
            return Self::from_tz_data(&fs::read("/etc/localtime")?);
        }

        let mut chars = tz_string.chars();
        if chars.next() == Some(':') {
            return Self::from_file(&mut get_tz_file(chars.as_str())?);
        }

        if let Ok(mut file) = get_tz_file(tz_string) {
            return Self::from_file(&mut file);
        }

        // TZ string extensions are not allowed
        let tz_string = tz_string.trim_matches(|c: char| c.is_ascii_whitespace());
        let rule = TransitionRule::from_tz_string(tz_string.as_bytes(), false)?;
        Ok(Self::new(
            vec![],
            match rule {
                TransitionRule::Fixed(local_time_type) => vec![local_time_type],
                TransitionRule::Alternate(AlternateTime { std, dst, .. }) => vec![std, dst],
            },
            vec![],
            Some(rule),
        )?)
    }

    /// Construct a time zone
    pub fn new(
        transitions: Vec<Transition>,
        local_time_types: Vec<LocalTimeType>,
        leap_seconds: Vec<LeapSecond>,
        extra_rule: Option<TransitionRule>,
    ) -> Result<Self, TimeZoneError> {
        TimeZoneRef::new_unchecked(&transitions, &local_time_types, &leap_seconds, &extra_rule)
            .check_inputs()?;
        Ok(Self { transitions, local_time_types, leap_seconds, extra_rule })
    }

    /// Construct a time zone from the contents of a time zone file
    pub fn from_file(file: &mut File) -> Result<Self, TzError> {
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)?;
        Self::from_tz_data(&bytes)
    }

    /// Construct a time zone from the contents of a time zone file
    ///
    /// Parse TZif data as described in [RFC 8536](https://datatracker.ietf.org/doc/html/rfc8536).
    pub fn from_tz_data(bytes: &[u8]) -> Result<Self, TzError> {
        let mut cursor = Cursor::new(bytes);
        let data_block = DataBlock::new(&mut cursor, true)?;
        match data_block.header.version {
            Version::V1 => match cursor.is_empty() {
                true => data_block.parse(None),
                false => {
                    return Err(TzFileError::InvalidTzFile(
                        "remaining data after end of TZif v1 data block",
                    )
                    .into())
                }
            },
            Version::V2 | Version::V3 => {
                let data_block = DataBlock::new(&mut cursor, false)?;
                data_block.parse(Some(cursor.remaining()))
            }
        }
    }

    /// Construct a time zone with the specified UTC offset in seconds
    pub fn fixed(ut_offset: i32) -> Result<Self, LocalTimeTypeError> {
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

    /// Find the current local time type associated to the time zone
    pub fn find_current_local_time_type(&self) -> Result<&LocalTimeType, TzError> {
        Ok(self.find_local_time_type(
            SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?.as_secs().try_into()?,
        )?)
    }

    /// Find the local time type associated to the time zone at the specified Unix time in seconds
    pub fn find_local_time_type(
        &self,
        unix_time: i64,
    ) -> Result<&LocalTimeType, FindLocalTimeTypeError> {
        self.as_ref().find_local_time_type(unix_time)
    }

    /// Returns a reference to the time zone
    pub fn as_ref(&self) -> TimeZoneRef {
        TimeZoneRef::new_unchecked(
            &self.transitions,
            &self.local_time_types,
            &self.leap_seconds,
            &self.extra_rule,
        )
    }
}

/// Open the TZif file corresponding to a TZ string
pub(crate) fn get_tz_file(tz_string: &str) -> Result<File, TzFileError> {
    // Don't check system timezone directories on non-UNIX platforms
    #[cfg(not(unix))]
    return Ok(File::open(tz_string)?);

    #[cfg(unix)]
    {
        // Possible system timezone directories
        const ZONE_INFO_DIRECTORIES: [&str; 3] =
            ["/usr/share/zoneinfo", "/share/zoneinfo", "/etc/zoneinfo"];

        if tz_string.starts_with('/') {
            Ok(File::open(tz_string)?)
        } else {
            for folder in &ZONE_INFO_DIRECTORIES {
                if let Ok(file) = File::open(format!("{}/{}", folder, tz_string)) {
                    return Ok(file);
                }
            }
            Err(TzFileError::IoError(io::ErrorKind::NotFound.into()))
        }
    }
}

/// TZif version
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Version {
    /// Version 1
    V1,
    /// Version 2
    V2,
    /// Version 3
    V3,
}

/// TZif header
#[derive(Debug)]
struct Header {
    /// TZif version
    version: Version,
    /// Number of UT/local indicators
    ut_local_count: usize,
    /// Number of standard/wall indicators
    std_wall_count: usize,
    /// Number of leap-second records
    leap_count: usize,
    /// Number of transition times
    transition_count: usize,
    /// Number of local time type records
    type_count: usize,
    /// Number of time zone designations bytes
    char_count: usize,
}

impl Header {
    fn new(cursor: &mut Cursor) -> Result<Self, TzFileError> {
        let magic = cursor.read_exact(4)?;
        if magic != *b"TZif" {
            return Err(TzFileError::InvalidTzFile("invalid magic number"));
        }

        let version = match cursor.read_exact(1)? {
            [0x00] => Version::V1,
            [0x32] => Version::V2,
            [0x33] => Version::V3,
            _ => return Err(TzFileError::UnsupportedTzFile("unsupported TZif version")),
        };

        cursor.read_exact(15)?;
        let ut_local_count = cursor.read_be_u32()?;
        let std_wall_count = cursor.read_be_u32()?;
        let leap_count = cursor.read_be_u32()?;
        let transition_count = cursor.read_be_u32()?;
        let type_count = cursor.read_be_u32()?;
        let char_count = cursor.read_be_u32()?;

        if !(type_count != 0
            && char_count != 0
            && (ut_local_count == 0 || ut_local_count == type_count)
            && (std_wall_count == 0 || std_wall_count == type_count))
        {
            return Err(TzFileError::InvalidTzFile("invalid header"));
        }

        Ok(Self {
            version,
            ut_local_count: ut_local_count as usize,
            std_wall_count: std_wall_count as usize,
            leap_count: leap_count as usize,
            transition_count: transition_count as usize,
            type_count: type_count as usize,
            char_count: char_count as usize,
        })
    }
}

/// TZif data blocks
struct DataBlock<'a> {
    header: Header,
    /// Time size in bytes
    time_size: usize,
    /// Transition times data block
    transition_times: &'a [u8],
    /// Transition types data block
    transition_types: &'a [u8],
    /// Local time types data block
    local_time_types: &'a [u8],
    /// Time zone designations data block
    time_zone_designations: &'a [u8],
    /// Leap seconds data block
    leap_seconds: &'a [u8],
    /// UT/local indicators data block
    std_walls: &'a [u8],
    /// Standard/wall indicators data block
    ut_locals: &'a [u8],
}

impl<'a> DataBlock<'a> {
    /// Read TZif data blocks
    fn new(cursor: &mut Cursor<'a>, first: bool) -> Result<Self, TzFileError> {
        let header = Header::new(cursor)?;
        let time_size = match first {
            true => 4, // We always parse V1 first
            false => 8,
        };

        Ok(Self {
            time_size,
            transition_times: cursor.read_exact(header.transition_count * time_size)?,
            transition_types: cursor.read_exact(header.transition_count)?,
            local_time_types: cursor.read_exact(header.type_count * 6)?,
            time_zone_designations: cursor.read_exact(header.char_count)?,
            leap_seconds: cursor.read_exact(header.leap_count * (time_size + 4))?,
            std_walls: cursor.read_exact(header.std_wall_count)?,
            ut_locals: cursor.read_exact(header.ut_local_count)?,
            header,
        })
    }

    /// Parse time values
    fn parse_time(&self, arr: &[u8], version: Version) -> Result<i64, TzFileError> {
        Ok(match version {
            Version::V1 => i32::from_be_bytes(arr.try_into()?).into(),
            Version::V2 | Version::V3 => i64::from_be_bytes(arr.try_into()?),
        })
    }

    /// Parse time zone data
    fn parse(&self, footer: Option<&[u8]>) -> Result<TimeZone, TzError> {
        let mut transitions = Vec::with_capacity(self.header.transition_count);
        for (arr_time, &local_time_type_index) in
            self.transition_times.chunks_exact(self.time_size).zip(self.transition_types)
        {
            let unix_leap_time =
                self.parse_time(&arr_time[0..self.time_size], self.header.version)?;
            let local_time_type_index = local_time_type_index as usize;
            transitions.push(Transition::new(unix_leap_time, local_time_type_index));
        }

        let mut local_time_types = Vec::with_capacity(self.header.type_count);
        for arr in self.local_time_types.chunks_exact(6) {
            let ut_offset = i32::from_be_bytes(arr[0..4].try_into()?);

            let is_dst = match arr[4] {
                0 => false,
                1 => true,
                _ => return Err(TzFileError::InvalidTzFile("invalid DST indicator").into()),
            };

            let char_index = arr[5] as usize;
            if char_index >= self.header.char_count {
                return Err(
                    TzFileError::InvalidTzFile("invalid time zone designation char index").into()
                );
            }

            let time_zone_designation =
                match self.time_zone_designations[char_index..].iter().position(|&c| c == b'\0') {
                    None => {
                        return Err(TzFileError::InvalidTzFile(
                            "invalid time zone designation char index",
                        )
                        .into())
                    }
                    Some(position) => {
                        let time_zone_designation =
                            &self.time_zone_designations[char_index..char_index + position];

                        if !time_zone_designation.is_empty() {
                            Some(time_zone_designation)
                        } else {
                            None
                        }
                    }
                };

            local_time_types.push(LocalTimeType::new(ut_offset, is_dst, time_zone_designation)?);
        }

        let mut leap_seconds = Vec::with_capacity(self.header.leap_count);
        for arr in self.leap_seconds.chunks_exact(self.time_size + 4) {
            let unix_leap_time = self.parse_time(&arr[0..self.time_size], self.header.version)?;
            let correction =
                i32::from_be_bytes(arr[self.time_size..self.time_size + 4].try_into()?);
            leap_seconds.push(LeapSecond::new(unix_leap_time, correction));
        }

        let std_walls_iter = self.std_walls.iter().copied().chain(iter::repeat(0));
        let ut_locals_iter = self.ut_locals.iter().copied().chain(iter::repeat(0));
        for (std_wall, ut_local) in std_walls_iter.zip(ut_locals_iter).take(self.header.type_count)
        {
            if !matches!((std_wall, ut_local), (0, 0) | (1, 0) | (1, 1)) {
                return Err(TzFileError::InvalidTzFile(
                    "invalid couple of standard/wall and UT/local indicators",
                )
                .into());
            }
        }

        let extra_rule = match footer {
            Some(footer) => {
                let footer = str::from_utf8(footer)?;
                if !(footer.starts_with('\n') && footer.ends_with('\n')) {
                    return Err(TzFileError::InvalidTzFile("invalid footer").into());
                }

                let tz_string = footer.trim_matches(|c: char| c.is_ascii_whitespace());
                if tz_string.starts_with(':') || tz_string.contains('\0') {
                    return Err(TzFileError::InvalidTzFile("invalid footer").into());
                }

                match tz_string.is_empty() {
                    true => None,
                    false => Some(TransitionRule::from_tz_string(
                        tz_string.as_bytes(),
                        self.header.version == Version::V3,
                    )?),
                }
            }
            None => None,
        };

        Ok(TimeZone::new(transitions, local_time_types, leap_seconds, extra_rule)?)
    }
}

/// Number of seconds in one week
const SECONDS_PER_WEEK: i64 = SECONDS_PER_DAY * DAYS_PER_WEEK;
/// Number of seconds in 28 days
const SECONDS_PER_28_DAYS: i64 = SECONDS_PER_DAY * 28;

const UTC_TYPE: LocalTimeType = LocalTimeType::utc();
