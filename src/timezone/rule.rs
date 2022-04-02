use std::cmp::Ordering;

use super::parser::Cursor;
use super::{LocalTimeType, SECONDS_PER_WEEK};
use crate::datetime::{days_since_unix_epoch, is_leap_year, UtcDateTime};
use crate::{
    Error, CUMUL_DAY_IN_MONTHS_NORMAL_YEAR, DAYS_PER_WEEK, DAY_IN_MONTHS_NORMAL_YEAR,
    SECONDS_PER_DAY,
};

/// Transition rule
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(super) enum TransitionRule {
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
    pub(super) fn from_tz_string(
        tz_string: &[u8],
        use_string_extensions: bool,
    ) -> Result<Self, Error> {
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
                return Err(Error::UnsupportedTzString("DST start and end rules must be provided"))
            }
        };

        if cursor.is_empty() {
            return Err(Error::UnsupportedTzString("DST start and end rules must be provided"));
        }

        cursor.read_tag(b",")?;
        let (dst_start, dst_start_time) = RuleDay::parse(&mut cursor, use_string_extensions)?;

        cursor.read_tag(b",")?;
        let (dst_end, dst_end_time) = RuleDay::parse(&mut cursor, use_string_extensions)?;

        if !cursor.is_empty() {
            return Err(Error::InvalidTzString("remaining data after parsing TZ string"));
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
    pub(super) fn find_local_time_type(&self, unix_time: i64) -> Result<&LocalTimeType, Error> {
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

/// Transition rule representing alternate local time types
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(super) struct AlternateTime {
    /// Local time type for standard time
    pub(super) std: LocalTimeType,
    /// Local time type for Daylight Saving Time
    pub(super) dst: LocalTimeType,
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
    fn new(
        std: LocalTimeType,
        dst: LocalTimeType,
        dst_start: RuleDay,
        dst_start_time: i32,
        dst_end: RuleDay,
        dst_end_time: i32,
    ) -> Result<Self, Error> {
        // Overflow is not possible
        if !((dst_start_time as i64).abs() < SECONDS_PER_WEEK
            && (dst_end_time as i64).abs() < SECONDS_PER_WEEK)
        {
            return Err(Error::TransitionRule("invalid DST start or end time"));
        }

        Ok(Self { std, dst, dst_start, dst_start_time, dst_end, dst_end_time })
    }

    /// Find the local time type associated to the alternate transition rule at the specified Unix time in seconds
    fn find_local_time_type(&self, unix_time: i64) -> Result<&LocalTimeType, Error> {
        // Overflow is not possible
        let dst_start_time_in_utc = self.dst_start_time as i64 - self.std.ut_offset as i64;
        let dst_end_time_in_utc = self.dst_end_time as i64 - self.dst.ut_offset as i64;

        let current_year = match UtcDateTime::from_timespec(unix_time, 0) {
            Ok(utc_date_time) => utc_date_time.year(),
            Err(error) => return Err(error),
        };

        // Check if the current year is valid for the following computations
        if !(i32::MIN + 2 <= current_year && current_year <= i32::MAX - 2) {
            return Err(Error::OutOfRange("out of range date time"));
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
fn parse_time_zone_designation<'a>(cursor: &mut Cursor<'a>) -> Result<&'a [u8], Error> {
    match cursor.peek() {
        Some(b'<') => {}
        _ => return Ok(cursor.read_while(u8::is_ascii_alphabetic)?),
    }

    cursor.read_exact(1)?;
    let unquoted = cursor.read_until(|&x| x == b'>')?;
    cursor.read_exact(1)?;
    Ok(unquoted)
}

/// Parse time zone offset
fn parse_offset(cursor: &mut Cursor) -> Result<i32, Error> {
    let (sign, hour, minute, second) = parse_signed_hhmmss(cursor)?;

    if !(0..=24).contains(&hour) {
        return Err(Error::InvalidTzString("invalid offset hour"));
    }
    if !(0..=59).contains(&minute) {
        return Err(Error::InvalidTzString("invalid offset minute"));
    }
    if !(0..=59).contains(&second) {
        return Err(Error::InvalidTzString("invalid offset second"));
    }

    Ok(sign * (hour * 3600 + minute * 60 + second))
}

/// Parse transition rule time
fn parse_rule_time(cursor: &mut Cursor) -> Result<i32, Error> {
    let (hour, minute, second) = parse_hhmmss(cursor)?;

    if !(0..=24).contains(&hour) {
        return Err(Error::InvalidTzString("invalid day time hour"));
    }
    if !(0..=59).contains(&minute) {
        return Err(Error::InvalidTzString("invalid day time minute"));
    }
    if !(0..=59).contains(&second) {
        return Err(Error::InvalidTzString("invalid day time second"));
    }

    Ok(hour * 3600 + minute * 60 + second)
}

/// Parse transition rule time with TZ string extensions
fn parse_rule_time_extended(cursor: &mut Cursor) -> Result<i32, Error> {
    let (sign, hour, minute, second) = parse_signed_hhmmss(cursor)?;

    if !(-167..=167).contains(&hour) {
        return Err(Error::InvalidTzString("invalid day time hour"));
    }
    if !(0..=59).contains(&minute) {
        return Err(Error::InvalidTzString("invalid day time minute"));
    }
    if !(0..=59).contains(&second) {
        return Err(Error::InvalidTzString("invalid day time second"));
    }

    Ok(sign * (hour * 3600 + minute * 60 + second))
}

/// Parse hours, minutes and seconds
fn parse_hhmmss(cursor: &mut Cursor) -> Result<(i32, i32, i32), Error> {
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
fn parse_signed_hhmmss(cursor: &mut Cursor) -> Result<(i32, i32, i32, i32), Error> {
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

/// Transition rule day
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum RuleDay {
    /// Julian day in `[1, 365]`, without taking occasional Feb 29 into account, which is not referenceable
    Julian1WithoutLeap(Julian1WithoutLeap),
    /// Zero-based Julian day in `[0, 365]`, taking occasional Feb 29 into account
    Julian0WithLeap(Julian0WithLeap),
    /// Day represented by a month, a month week and a week day
    MonthWeekDay(MonthWeekDay),
}

impl RuleDay {
    /// Parse transition rule
    fn parse(cursor: &mut Cursor, use_string_extensions: bool) -> Result<(Self, i32), Error> {
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
/// Julian day in `[1, 365]`, without taking occasional Feb 29 into account, which is not referenceable
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct Julian1WithoutLeap(u16);

impl Julian1WithoutLeap {
    /// Construct a transition rule day represented by a Julian day in `[1, 365]`, without taking occasional Feb 29 into account, which is not referenceable
    fn new(julian_day_1: u16) -> Result<Self, Error> {
        if !(1..=365).contains(&julian_day_1) {
            return Err(Error::TransitionRule("invalid rule day julian day"));
        }

        Ok(Self(julian_day_1))
    }
}

/// Zero-based Julian day in `[0, 365]`, taking occasional Feb 29 into account
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct Julian0WithLeap(u16);

impl Julian0WithLeap {
    /// Construct a transition rule day represented by a zero-based Julian day in `[0, 365]`, taking occasional Feb 29 into account
    fn new(julian_day_0: u16) -> Result<Self, Error> {
        if julian_day_0 > 365 {
            return Err(Error::TransitionRule("invalid rule day julian day"));
        }

        Ok(Self(julian_day_0))
    }
}

/// Day represented by a month, a month week and a week day
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct MonthWeekDay {
    /// Month in `[1, 12]`
    month: u8,
    /// Week of the month in `[1, 5]`, with `5` representing the last week of the month
    week: u8,
    /// Day of the week in `[0, 6]` from Sunday
    week_day: u8,
}

impl MonthWeekDay {
    /// Construct a transition rule day represented by a month, a month week and a week day
    fn new(month: u8, week: u8, week_day: u8) -> Result<Self, Error> {
        if !(1..=12).contains(&month) {
            return Err(Error::TransitionRule("invalid rule day month"));
        }

        if !(1..=5).contains(&week) {
            return Err(Error::TransitionRule("invalid rule day week"));
        }

        if week_day > 6 {
            return Err(Error::TransitionRule("invalid rule day week day"));
        }

        Ok(Self { month, week, week_day })
    }
}

#[cfg(test)]
mod tests {
    use super::super::Transition;
    use super::{
        AlternateTime, Julian0WithLeap, Julian1WithoutLeap, LocalTimeType, MonthWeekDay, RuleDay,
        TransitionRule,
    };
    use crate::{Error, TimeZone};

    #[test]
    fn test_quoted() -> Result<(), Error> {
        let transition_rule = TransitionRule::from_tz_string(b"<-03>+3<+03>-3,J1,J365", false)?;
        assert_eq!(
            transition_rule,
            AlternateTime::new(
                LocalTimeType::new(-10800, false, Some(b"-03"))?,
                LocalTimeType::new(10800, true, Some(b"+03"))?,
                RuleDay::from(Julian1WithoutLeap::new(1)?),
                7200,
                RuleDay::from(Julian1WithoutLeap::new(365)?),
                7200,
            )?
            .into()
        );
        Ok(())
    }

    #[test]
    fn test_full() -> Result<(), Error> {
        let tz_string = b"NZST-12:00:00NZDT-13:00:00,M10.1.0/02:00:00,M3.3.0/02:00:00";
        let transition_rule = TransitionRule::from_tz_string(tz_string, false)?;
        assert_eq!(
            transition_rule,
            AlternateTime::new(
                LocalTimeType::new(43200, false, Some(b"NZST"))?,
                LocalTimeType::new(46800, true, Some(b"NZDT"))?,
                RuleDay::from(MonthWeekDay::new(10, 1, 0)?),
                7200,
                RuleDay::from(MonthWeekDay::new(3, 3, 0)?),
                7200,
            )?
            .into()
        );
        Ok(())
    }

    #[test]
    fn test_negative_dst() -> Result<(), Error> {
        let tz_string = b"IST-1GMT0,M10.5.0,M3.5.0/1";
        let transition_rule = TransitionRule::from_tz_string(tz_string, false)?;
        assert_eq!(
            transition_rule,
            AlternateTime::new(
                LocalTimeType::new(3600, false, Some(b"IST"))?,
                LocalTimeType::new(0, true, Some(b"GMT"))?,
                RuleDay::from(MonthWeekDay::new(10, 5, 0)?),
                7200,
                RuleDay::from(MonthWeekDay::new(3, 5, 0)?),
                3600,
            )?
            .into()
        );
        Ok(())
    }

    #[test]
    fn test_negative_hour() -> Result<(), Error> {
        let tz_string = b"<-03>3<-02>,M3.5.0/-2,M10.5.0/-1";
        assert!(TransitionRule::from_tz_string(tz_string, false).is_err());

        assert_eq!(
            TransitionRule::from_tz_string(tz_string, true)?,
            AlternateTime::new(
                LocalTimeType::new(-10800, false, Some(b"-03"))?,
                LocalTimeType::new(-7200, true, Some(b"-02"))?,
                RuleDay::from(MonthWeekDay::new(3, 5, 0)?),
                -7200,
                RuleDay::from(MonthWeekDay::new(10, 5, 0)?),
                -3600,
            )?
            .into()
        );
        Ok(())
    }

    #[test]
    fn test_all_year_dst() -> Result<(), Error> {
        let tz_string = b"EST5EDT,0/0,J365/25";
        assert!(TransitionRule::from_tz_string(tz_string, false).is_err());

        assert_eq!(
            TransitionRule::from_tz_string(tz_string, true)?,
            AlternateTime::new(
                LocalTimeType::new(-18000, false, Some(b"EST"))?,
                LocalTimeType::new(-14400, true, Some(b"EDT"))?,
                RuleDay::from(Julian0WithLeap::new(0)?),
                0,
                RuleDay::from(Julian1WithoutLeap::new(365)?),
                90000,
            )?
            .into()
        );
        Ok(())
    }

    #[test]
    fn test_v3_file() -> Result<(), Error> {
        let bytes = b"TZif3\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x01\0\0\0\x04\0\0\x1c\x20\0\0IST\0TZif3\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x01\0\0\0\x01\0\0\0\0\0\0\0\x01\0\0\0\x01\0\0\0\x04\0\0\0\0\x7f\xe8\x17\x80\0\0\0\x1c\x20\0\0IST\0\x01\x01\x0aIST-2IDT,M3.4.4/26,M10.5.0\x0a";

        let time_zone = TimeZone::from_tz_data(bytes)?;

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
    fn test_rule_day() -> Result<(), Error> {
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
    fn test_transition_rule() -> Result<(), Error> {
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
    fn test_transition_rule_overflow() -> Result<(), Error> {
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
            Err(Error::OutOfRange(_))
        ));
        assert!(matches!(
            transition_rule_2.find_local_time_type(max_unix_time),
            Err(Error::OutOfRange(_))
        ));

        Ok(())
    }
}
