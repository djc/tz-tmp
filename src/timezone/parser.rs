use std::convert::TryInto;
use std::{iter, str};

use super::{LeapSecond, LocalTimeType, TimeZone, Transition, TransitionRule};
use crate::{Cursor, Error};

pub(super) fn parse(bytes: &[u8]) -> Result<TimeZone, Error> {
    let mut cursor = Cursor::new(bytes);
    let parser = Parser::new(&mut cursor, true)?;
    match parser.header.version {
        Version::V1 => match cursor.is_empty() {
            true => parser.parse(None),
            false => Err(Error::InvalidTzFile("remaining data after end of TZif v1 data block")),
        },
        Version::V2 | Version::V3 => {
            let parser = Parser::new(&mut cursor, false)?;
            parser.parse(Some(cursor.remaining()))
        }
    }
}

/// TZif data blocks
struct Parser<'a> {
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

impl<'a> Parser<'a> {
    /// Read TZif data blocks
    fn new(cursor: &mut Cursor<'a>, first: bool) -> Result<Self, Error> {
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
    fn parse_time(&self, arr: &[u8], version: Version) -> Result<i64, Error> {
        Ok(match version {
            Version::V1 => i32::from_be_bytes(arr.try_into()?).into(),
            Version::V2 | Version::V3 => i64::from_be_bytes(arr.try_into()?),
        })
    }

    /// Parse time zone data
    fn parse(self, footer: Option<&[u8]>) -> Result<TimeZone, Error> {
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
                _ => return Err(Error::InvalidTzFile("invalid DST indicator")),
            };

            let char_index = arr[5] as usize;
            if char_index >= self.header.char_count {
                return Err(Error::InvalidTzFile("invalid time zone designation char index"));
            }

            let time_zone_designation = match self.time_zone_designations[char_index..]
                .iter()
                .position(|&c| c == b'\0')
            {
                None => {
                    return Err(Error::InvalidTzFile("invalid time zone designation char index"))
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
                return Err(Error::InvalidTzFile(
                    "invalid couple of standard/wall and UT/local indicators",
                ));
            }
        }

        let extra_rule = match footer {
            Some(footer) => {
                let footer = str::from_utf8(footer)?;
                if !(footer.starts_with('\n') && footer.ends_with('\n')) {
                    return Err(Error::InvalidTzFile("invalid footer"));
                }

                let tz_string = footer.trim_matches(|c: char| c.is_ascii_whitespace());
                if tz_string.starts_with(':') || tz_string.contains('\0') {
                    return Err(Error::InvalidTzFile("invalid footer"));
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

        TimeZone::new(transitions, local_time_types, leap_seconds, extra_rule)
    }
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
    fn new(cursor: &mut Cursor) -> Result<Self, Error> {
        let magic = cursor.read_exact(4)?;
        if magic != *b"TZif" {
            return Err(Error::InvalidTzFile("invalid magic number"));
        }

        let version = match cursor.read_exact(1)? {
            [0x00] => Version::V1,
            [0x32] => Version::V2,
            [0x33] => Version::V3,
            _ => return Err(Error::UnsupportedTzFile("unsupported TZif version")),
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
            return Err(Error::InvalidTzFile("invalid header"));
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
