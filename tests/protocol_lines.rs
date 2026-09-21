//! The search over what arrives at the registry, rather than over what a
//! correct node would send.
//!
//! The generator, the registry and the oracles live in
//! `tests/scenario_body/mod.rs`, shared with the two turmoil targets for the
//! reason stated there: a second copy of a rule is a second place for it to be
//! wrong.
//!
//! This walk exists because the other one structurally cannot find what it
//! finds. `Action::from_pair` emits only well-formed requests, so a guard
//! against a malformed one is unreachable from it however long it counts —
//! and the guards against malformed requests are most of the guards the
//! registry has. Six of them were reached by hand, one test each, after a
//! reviewer pointed at each in turn. This is the instrument for the seventh.
//!
//! It is also very cheap. Nothing here is simulated: the registry is driven
//! directly, so this walk covers four times the seeds of the scenario walk in
//! a fraction of a second.

#[path = "scenario_body/mod.rs"]
mod body;

use body::{coverage_floor, env_u64, run_protocol, ProtocolRun, Served, FLOOR_WINDOW};

/// The seeds that have failed before, from `tests/seeds/protocol.txt`.
fn committed_seeds() -> Vec<u64> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/seeds/protocol.txt");
    let Ok(text) = std::fs::read_to_string(&path) else {
        panic!(
            "{} is missing: the regression corpus has to exist for this test to \
             be replaying anything",
            path.display()
        );
    };
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            line.parse()
                .unwrap_or_else(|_| panic!("`{line}` in protocol.txt is not a u64 seed"))
        })
        .collect()
}

#[test]
fn arbitrary_protocol_lines_hold_their_invariants() {
    let seeds = env_u64("JETSTREAM_PROTOCOL_SEEDS", 1024);
    let start = env_u64("JETSTREAM_PROTOCOL_START", 0);
    let end = body::window_end(start, seeds);

    // Every seed that has ever failed, replayed first, and counted separately
    // from the sweep for the reason the scenario walk states: a floor that a
    // regression replay can satisfy on the window's behalf has quietly stopped
    // checking the window.
    for seed in committed_seeds() {
        run_protocol(&ProtocolRun::from_seed(seed))
            .unwrap_or_else(|e| panic!("committed protocol seed {seed} regressed: {e}"));
    }

    println!("searching protocol seeds {start}..{end}");
    let mut totals = Served::default();
    for seed in start..end {
        let served = run_protocol(&ProtocolRun::from_seed(seed))
            .unwrap_or_else(|e| panic!("protocol seed {seed} failed: {e}"));
        totals.accepted += served.accepted;
        totals.refused += served.refused;
        totals.writes += served.writes;
        totals.transfers += served.transfers;
        totals.corrupted += served.corrupted;
        totals.junk += served.junk;
        totals.empty += served.empty;
        totals.spoofed += served.spoofed;
        totals.owed_refusals += served.owed_refusals;
    }

    println!(
        "searched protocol seeds {start}..{end}: {} requests served, {} refused, \
         {} writes accepted, {} handovers completed",
        totals.accepted, totals.refused, totals.writes, totals.transfers
    );
    println!(
        "  of which generated: {} corrupted, {} junk, {} empty, {} misdirected; \
         {} requests were owed a refusal in every state",
        totals.corrupted, totals.junk, totals.empty, totals.spoofed, totals.owed_refusals
    );

    // The vacuity check, and this search needs one more than the other does.
    // A generator that emitted nothing but garbage would be refused at the
    // parser every time and satisfy every oracle by never reaching one — and
    // the refusals would look like diligence. So the floor is on requests that
    // got *through*: the registry has to have been driven somewhere before its
    // guards mean anything.
    let window = end - start;
    let Some(floor) = coverage_floor(window) else {
        println!(
            "window of {window} seeds is below {FLOOR_WINDOW}: too short for a \
             rate to mean anything, so the coverage floor is not applied"
        );
        return;
    };
    assert!(
        totals.accepted as u64 > floor,
        "the generated lines must actually reach the registry; saw \
         {} served over seeds {start}..{end}, wanted more than {floor}",
        totals.accepted
    );

    // And the other half of the same claim: that malformed input is being
    // generated at all.
    //
    // This used to be a floor on *refusals*, and that floor was worth nothing.
    // `NONE`, `NO` and `FENCED` are ordinary answers to well-formed,
    // authenticated requests — a poll when the actor is held, an acquire that
    // was never offered, a write at a burned epoch — so a search that had
    // stopped generating malformed input entirely would still be refused
    // constantly. Measured, not argued: deleting every malformed generation
    // mode and leaving only `well_formed` left this walk green with a *higher*
    // refusal count than before. The check written specifically to stop a
    // check from saying nothing was itself saying nothing.
    //
    // So the floors are on what the generator produced. Each mode is counted
    // where it is built, and deleting any one of them takes its count to zero.
    for (mode, count) in [
        ("corrupted", totals.corrupted),
        ("junk", totals.junk),
        ("empty", totals.empty),
        ("misdirected", totals.spoofed),
    ] {
        assert!(
            count as u64 > floor,
            "the search must keep generating {mode} lines; saw {count} of them \
             over seeds {start}..{end}, wanted more than {floor}"
        );
    }

    // And that the obligation check has something to check. It is the only
    // oracle here that reads the *request* rather than the log, so a search
    // that never produced an unconditionally-refusable line would satisfy it
    // vacuously — which is the shape of failure this whole block is about.
    assert!(
        totals.owed_refusals as u64 > floor,
        "the search must produce requests the registry owes a refusal in every \
         state; saw {} over seeds {start}..{end}, wanted more than {floor}",
        totals.owed_refusals
    );

    // Depth, which the two counts above do not measure. Polls alone would
    // satisfy both of them while the run never got as far as holding the
    // actor, and every guard worth attacking is downstream of that. The first
    // version of this generator reached *zero* writes over 1024 seeds and
    // would have passed the checks above comfortably; four rounds of
    // measurement fixed it, and this is what stops it regressing quietly.
    assert!(
        totals.writes as u64 > floor,
        "the search must reach the states the guards are about; saw {} writes \
         accepted over seeds {start}..{end}, wanted more than {floor}",
        totals.writes
    );
}

// ---------------------------------------------------------------------------
// The obligation itself
// ---------------------------------------------------------------------------
//
// `owed_for` is the one oracle here that reads the *request* rather than the
// log, so it is the one that can accuse a sound registry of a defect. Both
// ways it has done so were found by running it rather than by reading it, and
// both were the same mistake: dropping a refusal reason it could have known,
// which turns "some refusal is owed" into "this exact refusal is owed".
//
// These pin the rule in both directions. Relaxing the obligation is only safe
// while the strict cases stay strict, so they are tested together.

use body::{is_a_reply_to, owed_for, Owed, Peer};

#[test]
fn a_request_refusable_for_two_reasons_may_be_refused_either_way() {
    // The case that was found first. `FORCE` is the registry's own verb, so a
    // node sending it is unauthorised however badly the rest of the line is
    // mangled — and a registry that refuses strangers before parsing their
    // input is sound, not defective.
    let owed = owed_for("FORCE 41.0", Peer::Node(1));
    assert_eq!(owed, Owed { malformed: true, not_permitted: true });
    assert_eq!(owed.exact(), None, "either `ERR` or `NO` must be acceptable");

    // And the case that was one step further out, which the first fix missed.
    // The *sender* field is legible even though the epoch is not, so the
    // connection can be disbelieved without parsing the rest.
    let owed = owed_for("WRITE 0 junk", Peer::Control);
    assert_eq!(owed, Owed { malformed: true, not_permitted: true });
    assert_eq!(owed.exact(), None, "either `ERR` or `NO` must be acceptable");
}

#[test]
fn a_request_refusable_for_one_reason_must_be_refused_that_way() {
    // The other half of the same rule, and the half that gives it teeth. A
    // relaxation that swallowed these would accept any refusal for anything,
    // which is the vacuity this whole file is about.

    // Malformed and nothing else: the connection agrees with the line.
    let owed = owed_for("WRITE 0 junk", Peer::Node(0));
    assert_eq!(owed, Owed { malformed: true, not_permitted: false });
    assert_eq!(owed.exact(), Some("ERR"));

    // The surplus field the lenient parser used to drop, which is the shape
    // that makes this obligation worth having at all.
    let owed = owed_for("POLL junk 0", Peer::Node(0));
    assert_eq!(owed, Owed { malformed: true, not_permitted: false });
    assert_eq!(owed.exact(), Some("ERR"));

    // Not permitted and nothing else: a well-formed line on the wrong wire.
    let owed = owed_for("WRITE 0 41", Peer::Node(1));
    assert_eq!(owed, Owed { malformed: false, not_permitted: true });
    assert_eq!(owed.exact(), Some("NO"));
}

#[test]
fn a_permission_check_reads_its_own_field_not_the_whole_line() {
    // The third catch of one mistake, each a field further out, so it is
    // pinned as the rule rather than as a third case: an illegible field must
    // not hide the authority facts the legible ones carry.

    // The successor is legible and names a node that does not exist; the
    // sender field is not legible at all.
    let owed = owed_for("BEGIN junk 99", Peer::Node(0));
    assert_eq!(owed, Owed { malformed: true, not_permitted: true });
    assert_eq!(owed.exact(), None);

    // A forced revoke naming a successor that does not exist, with a surplus
    // field after it that does not parse.
    let owed = owed_for("FORCE 99 junk", Peer::Control);
    assert_eq!(owed, Owed { malformed: true, not_permitted: true });
    assert_eq!(owed.exact(), None);

    // And the sender field legible while a later one is not, which is the
    // case that was caught second.
    let owed = owed_for("WRITE 0 junk", Peer::Control);
    assert_eq!(owed, Owed { malformed: true, not_permitted: true });
    assert_eq!(owed.exact(), None);
}

#[test]
fn a_refusal_has_to_be_in_the_words_that_request_uses() {
    // A wrong-vocabulary refusal leaves the log *unchanged*, which is exactly
    // what a refusal is supposed to leave behind — so no log-reading oracle
    // can see it. Measured: with a refused `RELEASE` answered `FENCED`, and
    // again with a refused `ACQUIRE` answered `NONE`, the search passed 20 000
    // seeds apiece while the registry spoke a protocol no node parses.
    assert!(!is_a_reply_to("RELEASE 0 41", "FENCED"));
    assert!(!is_a_reply_to("ACQUIRE 0 41", "NONE"));
    assert!(!is_a_reply_to("POLL 0", "FENCED"));
    assert!(!is_a_reply_to("BEGIN 0 1", "GRANT 41"));

    // A write's `OK` carries the sequence number it landed at; nothing else's
    // does, and that distinction is what lets the generator tell an epoch the
    // registry named from a write's position in the log.
    assert!(is_a_reply_to("WRITE 0 41", "OK 3"));
    assert!(!is_a_reply_to("WRITE 0 41", "OK"));
    assert!(is_a_reply_to("ACQUIRE 0 41", "OK"));
    assert!(!is_a_reply_to("ACQUIRE 0 41", "OK 3"));

    // What each request does ask for.
    assert!(is_a_reply_to("POLL 0", "GRANT 41"));
    assert!(is_a_reply_to("POLL 0", "REVOKE 42"));
    assert!(is_a_reply_to("POLL 0", "NONE"));
    assert!(is_a_reply_to("WRITE 0 41", "FENCED"));
    assert!(is_a_reply_to("BEGIN 0 1", "OK"));
    assert!(is_a_reply_to("FORCE 1", "OK"));

    // Refusals are universal, including for a verb the protocol does not
    // have. Which refusal is *owed* is `owed_for`'s business, not this one's.
    for line in ["POLL 0", "WRITE 0 41", "RELEASE 0 41", "FORCE 1", "SHOUT 0"] {
        assert!(is_a_reply_to(line, "NO"), "{line} must be refusable `NO`");
        assert!(is_a_reply_to(line, "ERR"), "{line} must be refusable `ERR`");
    }

    // And a word the protocol does not have is never a reply to anything.
    assert!(!is_a_reply_to("POLL 0", "MAYBE"));
    assert!(!is_a_reply_to("SHOUT 0", "OK"));
}

#[test]
fn an_unknown_verb_carries_no_opinion_about_who_sent_it() {
    // The protocol has no rule about who may send a request it does not have,
    // so the sender field of one is not a sender field — it is a number in a
    // line that means nothing. Reading it as one would demand `NO` where only
    // `ERR` is owed, which is the same mistake pointing the other way.
    let owed = owed_for("SHOUT 0 41", Peer::Control);
    assert_eq!(owed, Owed { malformed: true, not_permitted: false });
    assert_eq!(owed.exact(), Some("ERR"));

    let owed = owed_for("", Peer::Node(0));
    assert_eq!(owed, Owed { malformed: true, not_permitted: false });
    assert_eq!(owed.exact(), Some("ERR"));
}
