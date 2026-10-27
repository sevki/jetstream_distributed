//! `Id::machine_id` and the parsing under it.
//!
//! The parser is tested on strings, because the machine's own id differs per
//! platform, container and CI image. `machine_id` itself is tested for what holds
//! wherever it works: it is stable, and it is what the parser makes of the
//! platform's string.
#![cfg(all(feature = "machine-uid", not(target_arch = "wasm32")))]

use jetstream_distributed::id::Id;

const HEX: &str = "b72098c7acdb0e3c0123456789abcdef";
const VALUE: u128 = 0xb72098c7_acdb_0e3c_0123_456789abcdef;

#[test]
fn a_bare_hex_string_is_the_number_it_spells() {
    assert_eq!(Id::from_machine_uid(HEX).unwrap(), Id(VALUE));
}

#[test]
fn linuxs_trailing_newline_is_ignored() {
    assert_eq!(
        Id::from_machine_uid(&format!("{HEX}\n")).unwrap(),
        Id(VALUE)
    );
}

#[test]
fn a_dashed_uuid_is_the_same_id_as_its_bare_form() {
    // macOS's IOPlatformUUID and Windows's MachineGuid are written like this.
    let dashed = "b72098c7-acdb-0e3c-0123-456789abcdef";
    assert_eq!(Id::from_machine_uid(dashed).unwrap(), Id(VALUE));
    assert_eq!(
        Id::from_machine_uid(dashed).unwrap(),
        Id::from_machine_uid(HEX).unwrap()
    );
}

#[test]
fn case_does_not_change_the_id() {
    assert_eq!(
        Id::from_machine_uid(&HEX.to_uppercase()).unwrap(),
        Id::from_machine_uid(HEX).unwrap()
    );
}

#[test]
fn the_extremes_are_ids_too() {
    assert_eq!(Id::from_machine_uid(&"0".repeat(32)).unwrap(), Id(0));
    assert_eq!(Id::from_machine_uid(&"f".repeat(32)).unwrap(), Id(u128::MAX));
}

#[test]
fn what_is_not_a_machine_id_is_refused() {
    for bad in [
        "",
        "\n",
        "ff",                                 // too short: from_str_radix would take it
        "+b72098c7acdb0e3c0123456789abcde",   // a leading '+' is not a digit
        &"f".repeat(33),                      // too long
        "g72098c7acdb0e3c0123456789abcdef",   // not hexadecimal
        "b72098c7 acdb0e3c0123456789abcdef",  // an interior space
        "b72098c7acdb0e3c0123456789abcde\u{e9}", // not ASCII
    ] {
        assert!(
            Id::from_machine_uid(bad).is_err(),
            "{bad:?} was taken for a machine id"
        );
    }
}

#[test]
fn the_machine_id_is_stable_across_calls() {
    // A container without /etc/machine-id has none to give: then it must say so
    // every time, not once.
    match (Id::machine_id(), Id::machine_id()) {
        (Ok(a), Ok(b)) => assert_eq!(a, b),
        (Err(_), Err(_)) => {}
        (a, b) => panic!("machine_id changed its mind: {a:?} then {b:?}"),
    }
}

#[cfg(target_os = "linux")]
#[test]
fn on_linux_it_is_what_the_machine_id_file_spells() {
    let Some(file) = ["/etc/machine-id", "/var/lib/dbus/machine-id"]
        .into_iter()
        .find_map(|path| std::fs::read_to_string(path).ok())
    else {
        // No file, no expectation: `machine_id` is allowed to refuse here.
        assert!(Id::machine_id().is_err());
        return;
    };
    assert_eq!(
        Id::machine_id().unwrap(),
        Id::from_machine_uid(&file).unwrap()
    );
}
