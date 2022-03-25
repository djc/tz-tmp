//! Types related to a time zone.

use super::{
    CUMUL_DAY_IN_MONTHS_NORMAL_YEAR, DAYS_PER_WEEK, DAY_IN_MONTHS_NORMAL_YEAR, SECONDS_PER_DAY,
};
use crate::datetime::{days_since_unix_epoch, is_leap_year};
use crate::error::{
    FindLocalTimeTypeError, LocalTimeTypeError, OutOfRangeError, TimeZoneError,
    TransitionRuleError, TzError, TzFileError, TzStringError,
};
use crate::parse::{parse_posix_tz, Cursor};
use crate::UtcDateTime;

use std::cmp::Ordering;
use std::convert::TryInto;
use std::fs::{self, File};
use std::io::{self, Read};
use std::time::SystemTime;
use std::{fmt, iter, str};

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
}

impl AlternateTime {
    /// Returns local time type for standard time
    pub fn std(&self) -> &LocalTimeType {
        &self.std
    }

    /// Returns local time type for Daylight Saving Time
    pub fn dst(&self) -> &LocalTimeType {
        &self.dst
    }

    /// Returns start day of Daylight Saving Time
    pub fn dst_start(&self) -> &RuleDay {
        &self.dst_start
    }

    /// Returns local start day time of Daylight Saving Time, in seconds
    pub fn dst_start_time(&self) -> i32 {
        self.dst_start_time
    }

    /// Returns end day of Daylight Saving Time
    pub fn dst_end(&self) -> &RuleDay {
        &self.dst_end
    }

    /// Returns local end day time of Daylight Saving Time, in seconds
    pub fn dst_end_time(&self) -> i32 {
        self.dst_end_time
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

/// Transition rule
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TransitionRule {
    /// Fixed local time type
    Fixed(LocalTimeType),
    /// Alternate local time types
    Alternate(AlternateTime),
}

impl TransitionRule {
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

const UTC_TYPE: LocalTimeType = LocalTimeType::utc();

impl TimeZone {
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

    /// Returns a reference to the time zone
    pub fn as_ref(&self) -> TimeZoneRef {
        TimeZoneRef::new_unchecked(
            &self.transitions,
            &self.local_time_types,
            &self.leap_seconds,
            &self.extra_rule,
        )
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

    /// Construct a time zone with the specified UTC offset in seconds
    pub fn fixed(ut_offset: i32) -> Result<Self, LocalTimeTypeError> {
        Ok(Self {
            transitions: Vec::new(),
            local_time_types: vec![LocalTimeType::with_ut_offset(ut_offset)?],
            leap_seconds: Vec::new(),
            extra_rule: None,
        })
    }

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

    /// Construct a time zone from the contents of a time zone file
    pub fn from_tz_data(bytes: &[u8]) -> Result<Self, TzError> {
        parse_tz_file(bytes)
    }

    /// Construct a time zone from a POSIX TZ string, as described in [the POSIX documentation of the `TZ` environment variable](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html).
    pub fn from_posix_tz(tz_string: &str) -> Result<Self, TzError> {
        if tz_string.is_empty() {
            return Err(TzError::TzStringError(TzStringError::InvalidTzString("empty TZ string")));
        }

        if tz_string == "localtime" {
            return parse_tz_file(&fs::read("/etc/localtime")?);
        }

        let read = |mut file: File| -> io::Result<_> {
            let mut bytes = Vec::new();
            file.read_to_end(&mut bytes)?;
            Ok(bytes)
        };

        let mut chars = tz_string.chars();
        if chars.next() == Some(':') {
            return parse_tz_file(&read(get_tz_file(chars.as_str())?)?);
        }

        match get_tz_file(tz_string) {
            Ok(file) => parse_tz_file(&read(file)?),
            Err(_) => {
                let tz_string = tz_string.trim_matches(|c: char| c.is_ascii_whitespace());

                // TZ string extensions are not allowed
                let rule = parse_posix_tz(tz_string.as_bytes(), false)?;

                let local_time_types = match rule {
                    TransitionRule::Fixed(local_time_type) => vec![local_time_type],
                    TransitionRule::Alternate(AlternateTime { std, dst, .. }) => vec![std, dst],
                };

                Ok(TimeZone::new(vec![], local_time_types, vec![], Some(rule))?)
            }
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
                    false => Some(parse_posix_tz(
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

/// Parse TZif file as described in [RFC 8536](https://datatracker.ietf.org/doc/html/rfc8536)
pub(crate) fn parse_tz_file(bytes: &[u8]) -> Result<TimeZone, TzError> {
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

/// Number of seconds in one week
const SECONDS_PER_WEEK: i64 = SECONDS_PER_DAY * DAYS_PER_WEEK;
/// Number of seconds in 28 days
const SECONDS_PER_28_DAYS: i64 = SECONDS_PER_DAY * 28;

#[cfg(test)]
mod test {
    use super::{
        parse_tz_file, AlternateTime, Julian0WithLeap, Julian1WithoutLeap, LeapSecond,
        LocalTimeType, MonthWeekDay, RuleDay, TimeZone, Transition, TransitionRule, TzAsciiStr,
    };
    use crate::error::{FindLocalTimeTypeError, LocalTimeTypeError, OutOfRangeError, TzError};

    #[test]
    fn test_v1_file_with_leap_seconds() -> Result<(), TzError> {
        let bytes = b"TZif\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x01\0\0\0\x01\0\0\0\x1b\0\0\0\0\0\0\0\x01\0\0\0\x04\0\0\0\0\0\0UTC\0\x04\xb2\x58\0\0\0\0\x01\x05\xa4\xec\x01\0\0\0\x02\x07\x86\x1f\x82\0\0\0\x03\x09\x67\x53\x03\0\0\0\x04\x0b\x48\x86\x84\0\0\0\x05\x0d\x2b\x0b\x85\0\0\0\x06\x0f\x0c\x3f\x06\0\0\0\x07\x10\xed\x72\x87\0\0\0\x08\x12\xce\xa6\x08\0\0\0\x09\x15\x9f\xca\x89\0\0\0\x0a\x17\x80\xfe\x0a\0\0\0\x0b\x19\x62\x31\x8b\0\0\0\x0c\x1d\x25\xea\x0c\0\0\0\x0d\x21\xda\xe5\x0d\0\0\0\x0e\x25\x9e\x9d\x8e\0\0\0\x0f\x27\x7f\xd1\x0f\0\0\0\x10\x2a\x50\xf5\x90\0\0\0\x11\x2c\x32\x29\x11\0\0\0\x12\x2e\x13\x5c\x92\0\0\0\x13\x30\xe7\x24\x13\0\0\0\x14\x33\xb8\x48\x94\0\0\0\x15\x36\x8c\x10\x15\0\0\0\x16\x43\xb7\x1b\x96\0\0\0\x17\x49\x5c\x07\x97\0\0\0\x18\x4f\xef\x93\x18\0\0\0\x19\x55\x93\x2d\x99\0\0\0\x1a\x58\x68\x46\x9a\0\0\0\x1b\0\0";

        let time_zone = parse_tz_file(bytes)?;

        let time_zone_result = TimeZone::new(
            Vec::new(),
            vec![LocalTimeType::new(0, false, Some(b"UTC"))?],
            vec![
                LeapSecond::new(78796800, 1),
                LeapSecond::new(94694401, 2),
                LeapSecond::new(126230402, 3),
                LeapSecond::new(157766403, 4),
                LeapSecond::new(189302404, 5),
                LeapSecond::new(220924805, 6),
                LeapSecond::new(252460806, 7),
                LeapSecond::new(283996807, 8),
                LeapSecond::new(315532808, 9),
                LeapSecond::new(362793609, 10),
                LeapSecond::new(394329610, 11),
                LeapSecond::new(425865611, 12),
                LeapSecond::new(489024012, 13),
                LeapSecond::new(567993613, 14),
                LeapSecond::new(631152014, 15),
                LeapSecond::new(662688015, 16),
                LeapSecond::new(709948816, 17),
                LeapSecond::new(741484817, 18),
                LeapSecond::new(773020818, 19),
                LeapSecond::new(820454419, 20),
                LeapSecond::new(867715220, 21),
                LeapSecond::new(915148821, 22),
                LeapSecond::new(1136073622, 23),
                LeapSecond::new(1230768023, 24),
                LeapSecond::new(1341100824, 25),
                LeapSecond::new(1435708825, 26),
                LeapSecond::new(1483228826, 27),
            ],
            None,
        )?;

        assert_eq!(time_zone, time_zone_result);

        Ok(())
    }

    #[test]
    fn test_v2_file() -> Result<(), TzError> {
        let bytes = b"TZif2\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x06\0\0\0\x06\0\0\0\0\0\0\0\x07\0\0\0\x06\0\0\0\x14\x80\0\0\0\xbb\x05\x43\x48\xbb\x21\x71\x58\xcb\x89\x3d\xc8\xd2\x23\xf4\x70\xd2\x61\x49\x38\xd5\x8d\x73\x48\x01\x02\x01\x03\x04\x01\x05\xff\xff\x6c\x02\0\0\xff\xff\x6c\x58\0\x04\xff\xff\x7a\x68\x01\x08\xff\xff\x7a\x68\x01\x0c\xff\xff\x7a\x68\x01\x10\xff\xff\x73\x60\0\x04LMT\0HST\0HDT\0HWT\0HPT\0\0\0\0\0\x01\0\0\0\0\0\x01\0TZif2\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x06\0\0\0\x06\0\0\0\0\0\0\0\x07\0\0\0\x06\0\0\0\x14\xff\xff\xff\xff\x74\xe0\x70\xbe\xff\xff\xff\xff\xbb\x05\x43\x48\xff\xff\xff\xff\xbb\x21\x71\x58\xff\xff\xff\xff\xcb\x89\x3d\xc8\xff\xff\xff\xff\xd2\x23\xf4\x70\xff\xff\xff\xff\xd2\x61\x49\x38\xff\xff\xff\xff\xd5\x8d\x73\x48\x01\x02\x01\x03\x04\x01\x05\xff\xff\x6c\x02\0\0\xff\xff\x6c\x58\0\x04\xff\xff\x7a\x68\x01\x08\xff\xff\x7a\x68\x01\x0c\xff\xff\x7a\x68\x01\x10\xff\xff\x73\x60\0\x04LMT\0HST\0HDT\0HWT\0HPT\0\0\0\0\0\x01\0\0\0\0\0\x01\0\x0aHST10\x0a";

        let time_zone = parse_tz_file(bytes)?;

        let time_zone_result = TimeZone::new(
            vec![
                Transition::new(-2334101314, 1),
                Transition::new(-1157283000, 2),
                Transition::new(-1155436200, 1),
                Transition::new(-880198200, 3),
                Transition::new(-769395600, 4),
                Transition::new(-765376200, 1),
                Transition::new(-712150200, 5),
            ],
            vec![
                LocalTimeType::new(-37886, false, Some(b"LMT"))?,
                LocalTimeType::new(-37800, false, Some(b"HST"))?,
                LocalTimeType::new(-34200, true, Some(b"HDT"))?,
                LocalTimeType::new(-34200, true, Some(b"HWT"))?,
                LocalTimeType::new(-34200, true, Some(b"HPT"))?,
                LocalTimeType::new(-36000, false, Some(b"HST"))?,
            ],
            Vec::new(),
            Some(TransitionRule::from(LocalTimeType::new(-36000, false, Some(b"HST"))?)),
        )?;

        assert_eq!(time_zone, time_zone_result);

        assert_eq!(
            *time_zone.find_local_time_type(-1156939200)?,
            LocalTimeType::new(-34200, true, Some(b"HDT"))?
        );
        assert_eq!(
            *time_zone.find_local_time_type(1546300800)?,
            LocalTimeType::new(-36000, false, Some(b"HST"))?
        );

        Ok(())
    }

    #[test]
    fn test_v3_file() -> Result<(), TzError> {
        let bytes = b"TZif3\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x01\0\0\0\x04\0\0\x1c\x20\0\0IST\0TZif3\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x01\0\0\0\x01\0\0\0\0\0\0\0\x01\0\0\0\x01\0\0\0\x04\0\0\0\0\x7f\xe8\x17\x80\0\0\0\x1c\x20\0\0IST\0\x01\x01\x0aIST-2IDT,M3.4.4/26,M10.5.0\x0a";

        let time_zone = parse_tz_file(bytes)?;

        let time_zone_result = TimeZone::new(
            vec![Transition::new(2145916800, 0)],
            vec![LocalTimeType::new(7200, false, Some(b"IST"))?],
            Vec::new(),
            Some(TransitionRule::from(AlternateTime::new(
                LocalTimeType::new(7200, false, Some(b"IST"))?,
                LocalTimeType::new(10800, true, Some(b"IDT"))?,
                RuleDay::from(MonthWeekDay::new(3, 4, 4)?),
                93600,
                RuleDay::from(MonthWeekDay::new(10, 5, 0)?),
                7200,
            )?)),
        )?;

        assert_eq!(time_zone, time_zone_result);

        Ok(())
    }

    #[test]
    fn test_tz_ascii_str() -> Result<(), crate::TzError> {
        assert!(matches!(TzAsciiStr::new(b""), Err(LocalTimeTypeError(_))));
        assert!(matches!(TzAsciiStr::new(b"1"), Err(LocalTimeTypeError(_))));
        assert!(matches!(TzAsciiStr::new(b"12"), Err(LocalTimeTypeError(_))));
        assert_eq!(TzAsciiStr::new(b"123")?.as_bytes(), b"123");
        assert_eq!(TzAsciiStr::new(b"1234")?.as_bytes(), b"1234");
        assert_eq!(TzAsciiStr::new(b"12345")?.as_bytes(), b"12345");
        assert_eq!(TzAsciiStr::new(b"123456")?.as_bytes(), b"123456");
        assert_eq!(TzAsciiStr::new(b"1234567")?.as_bytes(), b"1234567");
        assert!(matches!(TzAsciiStr::new(b"12345678"), Err(LocalTimeTypeError(_))));
        assert!(matches!(TzAsciiStr::new(b"123456789"), Err(LocalTimeTypeError(_))));
        assert!(matches!(TzAsciiStr::new(b"1234567890"), Err(LocalTimeTypeError(_))));

        assert!(matches!(TzAsciiStr::new(b"123\0\0\0"), Err(LocalTimeTypeError(_))));

        Ok(())
    }

    #[test]
    fn test_rule_day() -> Result<(), crate::TzError> {
        let rule_day_j1 = RuleDay::from(Julian1WithoutLeap::new(60)?);
        assert_eq!(rule_day_j1.transition_date(2000), (3, 1));
        assert_eq!(rule_day_j1.transition_date(2001), (3, 1));
        assert_eq!(rule_day_j1.unix_time(2000, 43200), 951912000);

        let rule_day_j0 = RuleDay::from(Julian0WithLeap::new(59)?);
        assert_eq!(rule_day_j0.transition_date(2000), (2, 29));
        assert_eq!(rule_day_j0.transition_date(2001), (3, 1));
        assert_eq!(rule_day_j0.unix_time(2000, 43200), 951825600);

        let rule_day_mwd = RuleDay::from(MonthWeekDay::new(2, 5, 2)?);
        assert_eq!(rule_day_mwd.transition_date(2000), (2, 29));
        assert_eq!(rule_day_mwd.transition_date(2001), (2, 27));
        assert_eq!(rule_day_mwd.unix_time(2000, 43200), 951825600);
        assert_eq!(rule_day_mwd.unix_time(2001, 43200), 983275200);

        Ok(())
    }

    #[test]
    fn test_transition_rule() -> Result<(), crate::TzError> {
        let transition_rule_fixed = TransitionRule::from(LocalTimeType::new(-36000, false, None)?);
        assert_eq!(transition_rule_fixed.find_local_time_type(0)?.ut_offset(), -36000);

        let transition_rule_dst = TransitionRule::from(AlternateTime::new(
            LocalTimeType::new(43200, false, Some(b"NZST"))?,
            LocalTimeType::new(46800, true, Some(b"NZDT"))?,
            RuleDay::from(MonthWeekDay::new(10, 1, 0)?),
            7200,
            RuleDay::from(MonthWeekDay::new(3, 3, 0)?),
            7200,
        )?);

        assert_eq!(transition_rule_dst.find_local_time_type(953384399)?.ut_offset(), 46800);
        assert_eq!(transition_rule_dst.find_local_time_type(953384400)?.ut_offset(), 43200);
        assert_eq!(transition_rule_dst.find_local_time_type(970322399)?.ut_offset(), 43200);
        assert_eq!(transition_rule_dst.find_local_time_type(970322400)?.ut_offset(), 46800);

        let transition_rule_negative_dst = TransitionRule::from(AlternateTime::new(
            LocalTimeType::new(3600, false, Some(b"IST"))?,
            LocalTimeType::new(0, true, Some(b"GMT"))?,
            RuleDay::from(MonthWeekDay::new(10, 5, 0)?),
            7200,
            RuleDay::from(MonthWeekDay::new(3, 5, 0)?),
            3600,
        )?);

        assert_eq!(transition_rule_negative_dst.find_local_time_type(954032399)?.ut_offset(), 0);
        assert_eq!(transition_rule_negative_dst.find_local_time_type(954032400)?.ut_offset(), 3600);
        assert_eq!(transition_rule_negative_dst.find_local_time_type(972781199)?.ut_offset(), 3600);
        assert_eq!(transition_rule_negative_dst.find_local_time_type(972781200)?.ut_offset(), 0);

        let transition_rule_negative_time_1 = TransitionRule::from(AlternateTime::new(
            LocalTimeType::new(0, false, None)?,
            LocalTimeType::new(0, true, None)?,
            RuleDay::from(Julian0WithLeap::new(100)?),
            0,
            RuleDay::from(Julian0WithLeap::new(101)?),
            -86500,
        )?);

        assert!(transition_rule_negative_time_1.find_local_time_type(8639899)?.is_dst());
        assert!(!transition_rule_negative_time_1.find_local_time_type(8639900)?.is_dst());
        assert!(!transition_rule_negative_time_1.find_local_time_type(8639999)?.is_dst());
        assert!(transition_rule_negative_time_1.find_local_time_type(8640000)?.is_dst());

        let transition_rule_negative_time_2 = TransitionRule::from(AlternateTime::new(
            LocalTimeType::new(-10800, false, Some(b"-03"))?,
            LocalTimeType::new(-7200, true, Some(b"-02"))?,
            RuleDay::from(MonthWeekDay::new(3, 5, 0)?),
            -7200,
            RuleDay::from(MonthWeekDay::new(10, 5, 0)?),
            -3600,
        )?);

        assert_eq!(
            transition_rule_negative_time_2.find_local_time_type(954032399)?.ut_offset(),
            -10800
        );
        assert_eq!(
            transition_rule_negative_time_2.find_local_time_type(954032400)?.ut_offset(),
            -7200
        );
        assert_eq!(
            transition_rule_negative_time_2.find_local_time_type(972781199)?.ut_offset(),
            -7200
        );
        assert_eq!(
            transition_rule_negative_time_2.find_local_time_type(972781200)?.ut_offset(),
            -10800
        );

        let transition_rule_all_year_dst = TransitionRule::from(AlternateTime::new(
            LocalTimeType::new(-18000, false, Some(b"EST"))?,
            LocalTimeType::new(-14400, true, Some(b"EDT"))?,
            RuleDay::from(Julian0WithLeap::new(0)?),
            0,
            RuleDay::from(Julian1WithoutLeap::new(365)?),
            90000,
        )?);

        assert_eq!(
            transition_rule_all_year_dst.find_local_time_type(946702799)?.ut_offset(),
            -14400
        );
        assert_eq!(
            transition_rule_all_year_dst.find_local_time_type(946702800)?.ut_offset(),
            -14400
        );

        Ok(())
    }

    #[test]
    fn test_transition_rule_overflow() -> Result<(), crate::TzError> {
        let transition_rule_1 = TransitionRule::from(AlternateTime::new(
            LocalTimeType::new(-1, false, None)?,
            LocalTimeType::new(-1, true, None)?,
            RuleDay::from(Julian1WithoutLeap::new(365)?),
            0,
            RuleDay::from(Julian1WithoutLeap::new(1)?),
            0,
        )?);

        let transition_rule_2 = TransitionRule::from(AlternateTime::new(
            LocalTimeType::new(1, false, None)?,
            LocalTimeType::new(1, true, None)?,
            RuleDay::from(Julian1WithoutLeap::new(365)?),
            0,
            RuleDay::from(Julian1WithoutLeap::new(1)?),
            0,
        )?);

        let min_unix_time = -67768100567971200;
        let max_unix_time = 67767976233532799;

        assert!(matches!(
            transition_rule_1.find_local_time_type(min_unix_time),
            Err(OutOfRangeError(_))
        ));
        assert!(matches!(
            transition_rule_2.find_local_time_type(max_unix_time),
            Err(OutOfRangeError(_))
        ));

        Ok(())
    }

    #[test]
    fn test_time_zone() -> Result<(), crate::TzError> {
        let utc = LocalTimeType::utc();
        let cet = LocalTimeType::with_ut_offset(3600)?;

        let utc_local_time_types = vec![utc];
        let fixed_extra_rule = TransitionRule::from(cet);

        let time_zone_1 = TimeZone::new(vec![], utc_local_time_types.clone(), vec![], None)?;
        let time_zone_2 =
            TimeZone::new(vec![], utc_local_time_types.clone(), vec![], Some(fixed_extra_rule))?;
        let time_zone_3 =
            TimeZone::new(vec![Transition::new(0, 0)], utc_local_time_types.clone(), vec![], None)?;
        let time_zone_4 = TimeZone::new(
            vec![Transition::new(i32::MIN.into(), 0), Transition::new(0, 1)],
            vec![utc, cet],
            Vec::new(),
            Some(fixed_extra_rule),
        )?;

        assert_eq!(*time_zone_1.find_local_time_type(0)?, utc);
        assert_eq!(*time_zone_2.find_local_time_type(0)?, cet);

        assert_eq!(*time_zone_3.find_local_time_type(-1)?, utc);
        assert!(matches!(time_zone_3.find_local_time_type(0), Err(FindLocalTimeTypeError(_))));

        assert_eq!(*time_zone_4.find_local_time_type(-1)?, utc);
        assert_eq!(*time_zone_4.find_local_time_type(0)?, cet);

        let time_zone_err = TimeZone::new(
            vec![Transition::new(0, 0)],
            utc_local_time_types,
            vec![],
            Some(fixed_extra_rule),
        );
        assert!(time_zone_err.is_err());

        Ok(())
    }

    #[test]
    fn test_time_zone_from_posix_tz() -> Result<(), crate::TzError> {
        #[cfg(unix)]
        {
            let time_zone_local = TimeZone::local()?;
            let time_zone_local_1 = TimeZone::from_posix_tz("localtime")?;
            let time_zone_local_2 = TimeZone::from_posix_tz("/etc/localtime")?;
            let time_zone_local_3 = TimeZone::from_posix_tz(":/etc/localtime")?;

            assert_eq!(time_zone_local, time_zone_local_1);
            assert_eq!(time_zone_local, time_zone_local_2);
            assert_eq!(time_zone_local, time_zone_local_3);

            assert!(matches!(
                time_zone_local.find_current_local_time_type(),
                Ok(_) | Err(TzError::FindLocalTimeTypeError(_))
            ));

            let time_zone_utc = TimeZone::from_posix_tz("UTC")?;
            assert_eq!(time_zone_utc.find_local_time_type(0)?.ut_offset(), 0);
        }

        assert!(TimeZone::from_posix_tz("EST5EDT,0/0,J365/25").is_err());
        assert!(TimeZone::from_posix_tz("").is_err());

        Ok(())
    }

    #[test]
    fn test_leap_seconds() -> Result<(), crate::TzError> {
        let time_zone = TimeZone::new(
            Vec::new(),
            vec![LocalTimeType::new(0, false, Some(b"UTC"))?],
            vec![
                LeapSecond::new(78796800, 1),
                LeapSecond::new(94694401, 2),
                LeapSecond::new(126230402, 3),
                LeapSecond::new(157766403, 4),
                LeapSecond::new(189302404, 5),
                LeapSecond::new(220924805, 6),
                LeapSecond::new(252460806, 7),
                LeapSecond::new(283996807, 8),
                LeapSecond::new(315532808, 9),
                LeapSecond::new(362793609, 10),
                LeapSecond::new(394329610, 11),
                LeapSecond::new(425865611, 12),
                LeapSecond::new(489024012, 13),
                LeapSecond::new(567993613, 14),
                LeapSecond::new(631152014, 15),
                LeapSecond::new(662688015, 16),
                LeapSecond::new(709948816, 17),
                LeapSecond::new(741484817, 18),
                LeapSecond::new(773020818, 19),
                LeapSecond::new(820454419, 20),
                LeapSecond::new(867715220, 21),
                LeapSecond::new(915148821, 22),
                LeapSecond::new(1136073622, 23),
                LeapSecond::new(1230768023, 24),
                LeapSecond::new(1341100824, 25),
                LeapSecond::new(1435708825, 26),
                LeapSecond::new(1483228826, 27),
            ],
            None,
        )?;

        let time_zone_ref = time_zone.as_ref();

        assert!(matches!(time_zone_ref.unix_leap_time_to_unix_time(1136073621), Ok(1136073599)));
        assert!(matches!(time_zone_ref.unix_leap_time_to_unix_time(1136073622), Ok(1136073600)));
        assert!(matches!(time_zone_ref.unix_leap_time_to_unix_time(1136073623), Ok(1136073600)));
        assert!(matches!(time_zone_ref.unix_leap_time_to_unix_time(1136073624), Ok(1136073601)));

        assert!(matches!(time_zone_ref.unix_time_to_unix_leap_time(1136073599), Ok(1136073621)));
        assert!(matches!(time_zone_ref.unix_time_to_unix_leap_time(1136073600), Ok(1136073623)));
        assert!(matches!(time_zone_ref.unix_time_to_unix_leap_time(1136073601), Ok(1136073624)));

        Ok(())
    }

    #[test]
    fn test_leap_seconds_overflow() -> Result<(), crate::TzError> {
        let time_zone_err = TimeZone::new(
            vec![Transition::new(i64::MIN, 0)],
            vec![LocalTimeType::utc()],
            vec![LeapSecond::new(0, 1)],
            Some(TransitionRule::from(LocalTimeType::utc())),
        );
        assert!(time_zone_err.is_err());

        let time_zone = TimeZone::new(
            vec![Transition::new(i64::MAX, 0)],
            vec![LocalTimeType::utc()],
            vec![LeapSecond::new(0, 1)],
            None,
        )?;
        assert!(matches!(time_zone.find_local_time_type(i64::MAX), Err(FindLocalTimeTypeError(_))));

        Ok(())
    }
}
