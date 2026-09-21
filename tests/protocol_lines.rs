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

use body::{
    coverage_floor, env_u64, run_protocol, ProtocolRun, Served, FLOOR_WINDOW,
};

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
    }

    println!(
        "searched protocol seeds {start}..{end}: {} requests served, {} refused, \
         {} writes accepted, {} handovers completed",
        totals.accepted, totals.refused, totals.writes, totals.transfers
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

    // And the other half of the same claim. A generator that only ever
    // produced *valid* requests would be the action alphabet again, and would
    // reach none of the guards this search exists for. Refusals are the
    // evidence that malformed input is being generated at all.
    assert!(
        totals.refused as u64 > floor,
        "the generated lines must actually be malformed sometimes; saw \
         {} refused over seeds {start}..{end}, wanted more than {floor}",
        totals.refused
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
