//! Some useful constant functions.

use crate::timezone::{LeapSecond, Transition};

/// Macro for implementing binary search
macro_rules! impl_binary_search {
    ($slice:expr, $f:expr, $x:expr) => {{
        let mut size = $slice.len();
        let mut left = 0;
        let mut right = size;
        while left < right {
            let mid = left + size / 2;

            let v = $f(&$slice[mid]);
            if v < $x {
                left = mid + 1;
            } else if v > $x {
                right = mid;
            } else {
                return Ok(mid);
            }

            size = right - left;
        }
        Err(left)
    }};
}

/// Copy the input value
const fn copied(x: &i64) -> i64 {
    *x
}

/// Binary searches a sorted `i64` slice for the given element
pub fn binary_search_i64(slice: &[i64], x: i64) -> Result<usize, usize> {
    impl_binary_search!(slice, copied, x)
}

/// Binary searches a sorted `Transition` slice for the given element
pub fn binary_search_transitions(slice: &[Transition], x: i64) -> Result<usize, usize> {
    impl_binary_search!(slice, Transition::unix_leap_time, x)
}

/// Binary searches a sorted `LeapSecond` slice for the given element
pub fn binary_search_leap_seconds(slice: &[LeapSecond], x: i64) -> Result<usize, usize> {
    impl_binary_search!(slice, LeapSecond::unix_leap_time, x)
}
