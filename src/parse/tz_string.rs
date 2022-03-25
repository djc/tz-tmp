//! Functions used for parsing a TZ string.

use super::Cursor;
use crate::error::{TzError, TzStringError};
use crate::timezone::{
    AlternateTime, Julian0WithLeap, Julian1WithoutLeap, LocalTimeType, MonthWeekDay, RuleDay,
    TransitionRule,
};

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

/// Parse transition rule day
fn parse_rule_day(cursor: &mut Cursor) -> Result<RuleDay, TzError> {
    match cursor.peek() {
        Some(b'M') => {}
        Some(b'J') => {
            cursor.read_exact(1)?;
            return Ok(Julian1WithoutLeap::new(cursor.read_int()?)?.into());
        }
        _ => return Ok(Julian0WithLeap::new(cursor.read_int()?)?.into()),
    }

    cursor.read_exact(1)?;
    let month = cursor.read_int()?;
    cursor.read_tag(b".")?;
    let week = cursor.read_int()?;
    cursor.read_tag(b".")?;
    let week_day = cursor.read_int()?;
    Ok(MonthWeekDay::new(month, week, week_day)?.into())
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
    let date = parse_rule_day(cursor)?;

    let time = if cursor.read_optional_tag(b"/")? {
        if use_string_extensions {
            parse_rule_time_extended(cursor)?
        } else {
            parse_rule_time(cursor)?
        }
    } else {
        2 * 3600
    };

    Ok((date, time))
}

/// Parse a POSIX TZ string containing a time zone description, as described in [the POSIX documentation of the `TZ` environment variable](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html).
///
/// TZ string extensions from [RFC 8536](https://datatracker.ietf.org/doc/html/rfc8536#section-3.3.1) may be used.
///
pub(crate) fn parse_posix_tz(
    tz_string: &[u8],
    use_string_extensions: bool,
) -> Result<TransitionRule, TzError> {
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
        return Err(
            TzStringError::UnsupportedTzString("DST start and end rules must be provided").into()
        );
    }

    cursor.read_tag(b",")?;
    let (dst_start, dst_start_time) = parse_rule_block(&mut cursor, use_string_extensions)?;

    cursor.read_tag(b",")?;
    let (dst_end, dst_end_time) = parse_rule_block(&mut cursor, use_string_extensions)?;

    if !cursor.is_empty() {
        return Err(TzStringError::InvalidTzString("remaining data after parsing TZ string").into());
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

#[cfg(test)]
mod test {
    use super::parse_posix_tz;
    use crate::error::{TzError, TzStringError};
    use crate::timezone::{
        AlternateTime, Julian0WithLeap, Julian1WithoutLeap, LocalTimeType, MonthWeekDay, RuleDay,
    };

    #[test]
    fn test_no_dst() -> Result<(), TzError> {
        let tz_string = b"HST10";
        let transition_rule = parse_posix_tz(tz_string, false)?;
        assert_eq!(transition_rule, LocalTimeType::new(-36000, false, Some(b"HST"))?.into());
        Ok(())
    }

    #[test]
    fn test_quoted() -> Result<(), TzError> {
        let transition_rule = parse_posix_tz(b"<-03>+3<+03>-3,J1,J365", false)?;
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
    fn test_full() -> Result<(), TzError> {
        let tz_string = b"NZST-12:00:00NZDT-13:00:00,M10.1.0/02:00:00,M3.3.0/02:00:00";
        let transition_rule = parse_posix_tz(tz_string, false)?;
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
    fn test_negative_dst() -> Result<(), TzError> {
        let tz_string = b"IST-1GMT0,M10.5.0,M3.5.0/1";
        let transition_rule = parse_posix_tz(tz_string, false)?;
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
    fn test_negative_hour() -> Result<(), TzError> {
        let tz_string = b"<-03>3<-02>,M3.5.0/-2,M10.5.0/-1";
        assert!(parse_posix_tz(tz_string, false).is_err());

        assert_eq!(
            parse_posix_tz(tz_string, true)?,
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
    fn test_all_year_dst() -> Result<(), TzError> {
        let tz_string = b"EST5EDT,0/0,J365/25";
        assert!(parse_posix_tz(tz_string, false).is_err());

        assert_eq!(
            parse_posix_tz(tz_string, true)?,
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
    fn test_error() -> Result<(), TzError> {
        assert!(matches!(
            parse_posix_tz(b"IST-1GMT0", false),
            Err(TzError::TzStringError(TzStringError::UnsupportedTzString(_)))
        ));
        assert!(matches!(
            parse_posix_tz(b"EET-2EEST", false),
            Err(TzError::TzStringError(TzStringError::UnsupportedTzString(_)))
        ));

        Ok(())
    }
}
