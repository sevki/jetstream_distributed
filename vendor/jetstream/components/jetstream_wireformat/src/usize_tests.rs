//! `usize` on the wire.
//!
//! Golden bytes rather than round trips: a round trip passes on any single
//! target whatever width it uses, and the bug these guard against only
//! appears when the two ends are different targets.

use std::io::Cursor;

use crate::WireFormat;

fn encoded(value: usize) -> Vec<u8> {
    let mut bytes = Vec::new();
    value.encode(&mut bytes).expect("encoding a usize");
    bytes
}

// r[verify jetstream.wireformat.usize]
/// The same eight bytes on every target. A 32-bit target used to write only
/// the first four, which a 64-bit reader then took as half of the length.
#[test]
fn usize_is_eight_little_endian_bytes_on_every_target() {
    assert_eq!(encoded(3), [3, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(encoded(0x0403_0201), [1, 2, 3, 4, 0, 0, 0, 0]);
    assert_eq!(3usize.byte_size(), 8);
}

// r[verify jetstream.wireformat.usize]
#[test]
fn usize_reads_what_a_u64_writes() {
    let mut bytes = Vec::new();
    7u64.encode(&mut bytes).expect("encoding a u64");

    let mut cursor = Cursor::new(bytes);
    assert_eq!(usize::decode(&mut cursor).expect("decoding a usize"), 7);
    assert_eq!(cursor.position(), 8);
}

// r[verify jetstream.wireformat.usize]
/// A 64-bit peer can send a `usize` a 32-bit one cannot hold; that must be an
/// error, not a silently truncated length.
#[cfg(target_pointer_width = "32")]
#[test]
fn usize_too_wide_for_this_target_is_an_error_not_a_truncation() {
    let mut bytes = Vec::new();
    (u64::from(u32::MAX) + 1)
        .encode(&mut bytes)
        .expect("encoding a u64");

    let error = usize::decode(&mut Cursor::new(bytes)).expect_err("a usize wider than 32 bits");
    assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
}
