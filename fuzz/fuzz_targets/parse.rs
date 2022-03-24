#![no_main]
use libfuzzer_sys::fuzz_target;

use tz_rs::TimeZone;

fuzz_target!(|data: &[u8]| {
    TimeZone::from_tz_data(data);
});
