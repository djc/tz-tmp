//! Parsing functions.

use crate::error::{TzFileError, TzStringError};

mod tz_string;
pub(crate) use tz_string::parse_posix_tz;

use std::convert::TryInto;
use std::io::{Error, ErrorKind};
use std::num::ParseIntError;
use std::str::{self, FromStr};

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
