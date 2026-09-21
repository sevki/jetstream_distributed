//! Coverage-guided search over what arrives at the registry.
//!
//! The deterministic walk in `tests/protocol_lines.rs` counts seeds upwards,
//! which is cheap and reproducible and has no idea whether the next seed
//! reaches anything the last did not. This steers instead — and steering is
//! the point, because the states worth attacking are five or six aligned
//! requests deep and a blind walk reaches the deepest of them about five times
//! in a thousand runs.
//!
//! Both front ends drive the same generator, the same registry and the same
//! oracles. Nothing is duplicated here on purpose.
//!
//!     cargo +nightly fuzz run protocol
//!
//! A crash prints the failing step and the line that caused it. To turn one
//! into a permanent regression, add its seed to `tests/seeds/protocol.txt` if
//! the walk can reproduce it, or keep the input under `fuzz/corpus/protocol/`
//! if only the fuzzer can.

#![no_main]

#[path = "../../tests/scenario_body/mod.rs"]
mod body;

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // `None` means the input was too short to be a run at all, which is not a
    // finding — libFuzzer starts from nothing and has to be allowed to.
    if let Some(run) = body::ProtocolRun::from_bytes(data) {
        if let Err(why) = body::run_protocol(&run) {
            panic!("{why}");
        }
    }
});
