use super::{
    AlternateTime, Julian0WithLeap, Julian1WithoutLeap, LeapSecond, LocalTimeType, MonthWeekDay,
    RuleDay, TimeZone, Transition, TransitionRule, TzAsciiStr,
};
use crate::error::Error;

#[test]
fn test_no_dst() -> Result<(), Error> {
    let tz_string = b"HST10";
    let transition_rule = TransitionRule::from_tz_string(tz_string, false)?;
    assert_eq!(transition_rule, LocalTimeType::new(-36000, false, Some(b"HST"))?.into());
    Ok(())
}

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
fn test_error() -> Result<(), Error> {
    assert!(matches!(
        TransitionRule::from_tz_string(b"IST-1GMT0", false),
        Err(Error::UnsupportedTzString(_))
    ));
    assert!(matches!(
        TransitionRule::from_tz_string(b"EET-2EEST", false),
        Err(Error::UnsupportedTzString(_))
    ));

    Ok(())
}

#[test]
fn test_v1_file_with_leap_seconds() -> Result<(), Error> {
    let bytes = b"TZif\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x01\0\0\0\x01\0\0\0\x1b\0\0\0\0\0\0\0\x01\0\0\0\x04\0\0\0\0\0\0UTC\0\x04\xb2\x58\0\0\0\0\x01\x05\xa4\xec\x01\0\0\0\x02\x07\x86\x1f\x82\0\0\0\x03\x09\x67\x53\x03\0\0\0\x04\x0b\x48\x86\x84\0\0\0\x05\x0d\x2b\x0b\x85\0\0\0\x06\x0f\x0c\x3f\x06\0\0\0\x07\x10\xed\x72\x87\0\0\0\x08\x12\xce\xa6\x08\0\0\0\x09\x15\x9f\xca\x89\0\0\0\x0a\x17\x80\xfe\x0a\0\0\0\x0b\x19\x62\x31\x8b\0\0\0\x0c\x1d\x25\xea\x0c\0\0\0\x0d\x21\xda\xe5\x0d\0\0\0\x0e\x25\x9e\x9d\x8e\0\0\0\x0f\x27\x7f\xd1\x0f\0\0\0\x10\x2a\x50\xf5\x90\0\0\0\x11\x2c\x32\x29\x11\0\0\0\x12\x2e\x13\x5c\x92\0\0\0\x13\x30\xe7\x24\x13\0\0\0\x14\x33\xb8\x48\x94\0\0\0\x15\x36\x8c\x10\x15\0\0\0\x16\x43\xb7\x1b\x96\0\0\0\x17\x49\x5c\x07\x97\0\0\0\x18\x4f\xef\x93\x18\0\0\0\x19\x55\x93\x2d\x99\0\0\0\x1a\x58\x68\x46\x9a\0\0\0\x1b\0\0";

    let time_zone = TimeZone::from_tz_data(bytes)?;

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
fn test_v2_file() -> Result<(), Error> {
    let bytes = b"TZif2\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x06\0\0\0\x06\0\0\0\0\0\0\0\x07\0\0\0\x06\0\0\0\x14\x80\0\0\0\xbb\x05\x43\x48\xbb\x21\x71\x58\xcb\x89\x3d\xc8\xd2\x23\xf4\x70\xd2\x61\x49\x38\xd5\x8d\x73\x48\x01\x02\x01\x03\x04\x01\x05\xff\xff\x6c\x02\0\0\xff\xff\x6c\x58\0\x04\xff\xff\x7a\x68\x01\x08\xff\xff\x7a\x68\x01\x0c\xff\xff\x7a\x68\x01\x10\xff\xff\x73\x60\0\x04LMT\0HST\0HDT\0HWT\0HPT\0\0\0\0\0\x01\0\0\0\0\0\x01\0TZif2\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x06\0\0\0\x06\0\0\0\0\0\0\0\x07\0\0\0\x06\0\0\0\x14\xff\xff\xff\xff\x74\xe0\x70\xbe\xff\xff\xff\xff\xbb\x05\x43\x48\xff\xff\xff\xff\xbb\x21\x71\x58\xff\xff\xff\xff\xcb\x89\x3d\xc8\xff\xff\xff\xff\xd2\x23\xf4\x70\xff\xff\xff\xff\xd2\x61\x49\x38\xff\xff\xff\xff\xd5\x8d\x73\x48\x01\x02\x01\x03\x04\x01\x05\xff\xff\x6c\x02\0\0\xff\xff\x6c\x58\0\x04\xff\xff\x7a\x68\x01\x08\xff\xff\x7a\x68\x01\x0c\xff\xff\x7a\x68\x01\x10\xff\xff\x73\x60\0\x04LMT\0HST\0HDT\0HWT\0HPT\0\0\0\0\0\x01\0\0\0\0\0\x01\0\x0aHST10\x0a";

    let time_zone = TimeZone::from_tz_data(bytes)?;

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
fn test_tz_ascii_str() -> Result<(), Error> {
    assert!(matches!(TzAsciiStr::new(b""), Err(Error::LocalTimeType(_))));
    assert!(matches!(TzAsciiStr::new(b"1"), Err(Error::LocalTimeType(_))));
    assert!(matches!(TzAsciiStr::new(b"12"), Err(Error::LocalTimeType(_))));
    assert_eq!(TzAsciiStr::new(b"123")?.as_bytes(), b"123");
    assert_eq!(TzAsciiStr::new(b"1234")?.as_bytes(), b"1234");
    assert_eq!(TzAsciiStr::new(b"12345")?.as_bytes(), b"12345");
    assert_eq!(TzAsciiStr::new(b"123456")?.as_bytes(), b"123456");
    assert_eq!(TzAsciiStr::new(b"1234567")?.as_bytes(), b"1234567");
    assert!(matches!(TzAsciiStr::new(b"12345678"), Err(Error::LocalTimeType(_))));
    assert!(matches!(TzAsciiStr::new(b"123456789"), Err(Error::LocalTimeType(_))));
    assert!(matches!(TzAsciiStr::new(b"1234567890"), Err(Error::LocalTimeType(_))));

    assert!(matches!(TzAsciiStr::new(b"123\0\0\0"), Err(Error::LocalTimeType(_))));

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
    assert_eq!(transition_rule_negative_time_2.find_local_time_type(954032400)?.ut_offset(), -7200);
    assert_eq!(transition_rule_negative_time_2.find_local_time_type(972781199)?.ut_offset(), -7200);
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

    assert_eq!(transition_rule_all_year_dst.find_local_time_type(946702799)?.ut_offset(), -14400);
    assert_eq!(transition_rule_all_year_dst.find_local_time_type(946702800)?.ut_offset(), -14400);

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

#[test]
fn test_time_zone() -> Result<(), Error> {
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
    assert!(matches!(time_zone_3.find_local_time_type(0), Err(Error::FindLocalTimeType(_))));

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
fn test_time_zone_from_posix_tz() -> Result<(), Error> {
    #[cfg(unix)]
    {
        let time_zone_local = TimeZone::local()?;
        let time_zone_local_1 = TimeZone::from_posix_tz("localtime")?;
        let time_zone_local_2 = TimeZone::from_posix_tz("/etc/localtime")?;
        let time_zone_local_3 = TimeZone::from_posix_tz(":/etc/localtime")?;

        assert_eq!(time_zone_local, time_zone_local_1);
        assert_eq!(time_zone_local, time_zone_local_2);
        assert_eq!(time_zone_local, time_zone_local_3);

        let time_zone_utc = TimeZone::from_posix_tz("UTC")?;
        assert_eq!(time_zone_utc.find_local_time_type(0)?.ut_offset(), 0);
    }

    assert!(TimeZone::from_posix_tz("EST5EDT,0/0,J365/25").is_err());
    assert!(TimeZone::from_posix_tz("").is_err());

    Ok(())
}

#[test]
fn test_leap_seconds() -> Result<(), Error> {
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
fn test_leap_seconds_overflow() -> Result<(), Error> {
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
    assert!(matches!(time_zone.find_local_time_type(i64::MAX), Err(Error::FindLocalTimeType(_))));

    Ok(())
}
