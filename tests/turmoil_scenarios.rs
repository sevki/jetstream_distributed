//! The scenario search, and the replay of every seed it has ever found.
//!
//! The scenarios themselves — the actions, the oracles, the simulated network
//! they run on — live in `tests/scenario_body/mod.rs`, shared with the named
//! stories in `turmoil_ownership.rs` rather than duplicated: a runner and an
//! oracle that have drifted apart are worse than either alone, since both go
//! green while the thing they guard has moved underneath them.
//!
//! This is the blind half. It counts seeds upwards, which is cheap,
//! reproducible and has no idea what any of its scenarios were supposed to
//! reach. `Scenario::from_bytes` is there so a coverage-guided fuzzer could
//! drive the same runner instead — coverage is how you find the scenario
//! nobody would have counted up to — but no fuzz target is wired up in this
//! repository yet, so today that entry point is unused.

#[path = "scenario_body/mod.rs"]
mod body;

use body::{run_scenario, run_scenario_probed, Attempts, Event, Scenario};

/// The seeds that have failed before, from `tests/seeds/scenarios.txt`.
fn committed_seeds() -> Vec<u64> {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/seeds/scenarios.txt");
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
        .map(|line| line.parse().unwrap_or_else(|_| panic!("`{line}` in scenarios.txt is not a u64 seed")))
        .collect()
}

/// Read a `u64` from the environment, or fall back.
///
/// A malformed value falls back silently on purpose: this runs inside a test,
/// and a nightly job that dies on a typo in its own workflow finds nothing at
/// all.
fn env_u64(name: &str, fallback: u64) -> u64 {
    std::env::var(name).ok().and_then(|s| s.trim().parse().ok()).unwrap_or(fallback)
}

/// The search. Each seed is an independent story; a failure names the seed,
/// and `run_scenario(Scenario::from_seed(n))` replays it exactly.
#[test]
fn scenarios_hold_their_invariants() {
    // Deeper on demand: `JETSTREAM_SCENARIO_SEEDS=100000 cargo test --test
    // turmoil_scenarios` searches as long as you like, with the same runner and
    // the same oracles. The default is what CI can afford on every push.
    let seeds = env_u64("JETSTREAM_SCENARIO_SEEDS", 256);

    // Where the window starts. A search that always starts at zero is not a
    // search: it re-runs a fixed test suite at random-looking parameters and
    // cannot find anything it did not find the first time. A nightly job is
    // expected to pass a start that moves, so consecutive nights cover
    // adjacent, non-overlapping windows. Zero here keeps the default a fixed,
    // deterministic band, which is what a pull request wants: the same 256
    // scenarios on every push, so a red result means the change did it.
    let start = env_u64("JETSTREAM_SCENARIO_START", 0);
    let end = start.saturating_add(seeds);

    // Every seed that has ever failed, replayed first: a fixed bug stays
    // fixed, and one that is not yet fixed keeps this red until it is. The
    // sweep below searches for new ones; this makes sure the old ones cannot
    // come back unnoticed.
    // Counted separately from the search below, and deliberately not added to
    // it. The floor at the end is a claim about the *window* — that the seeds
    // in `start..end` still reach the fence — and a corpus write satisfies it
    // without any of them doing so. Today the corpus is empty and the two
    // sums are the same number; the first seed filed here is the moment that
    // stops being true, and a floor that a regression replay can satisfy on
    // the window's behalf is a floor that has quietly stopped checking
    // anything.
    let mut corpus_writes = 0usize;
    for seed in committed_seeds() {
        corpus_writes += run_scenario(Scenario::from_seed(seed))
            .unwrap_or_else(|e| panic!("committed seed {seed} regressed: {e}"));
    }

    // Named in the log so a failure says which window found it, and so a green
    // night is visibly a *different* green night from the one before it.
    println!("searching scenario seeds {start}..{end}");
    let mut writes = 0usize;
    let mut totals = Attempts::default();
    for seed in start..end {
        let (log, attempts) = run_scenario_probed(Scenario::from_seed(seed))
            .unwrap_or_else(|e| panic!("seed {seed} failed: {e}"));
        writes += log.iter().filter(|e| matches!(e, Event::Wrote { .. })).count();
        for a in attempts {
            totals.writes_sent += a.writes_sent;
            totals.writes_timed_out += a.writes_timed_out;
            totals.writes_failed += a.writes_failed;
        }
    }

    // A window in which no write was ever accepted would satisfy every oracle
    // above while exercising none of them: an empty log is exclusive, monotone
    // and capability-backed for free. This is the check on that.
    //
    // Proportional rather than a fixed count, because the window is
    // configurable and a fixed number would silently mean "fail on any small
    // window" the moment someone shortened it.
    //
    // The rate it is set against was measured rather than guessed. A model of
    // the generator over four 256-seed windows accepts between 82 and 111
    // writes per window, and an earlier real run of seeds 0..256 matched that
    // model's figure for its window to the write — so nothing is lost to the
    // network, and the settle window in the runner is wide enough that a step
    // ordinarily finishes before the next is queued. One accepted write per
    // sixteen seeds sits a factor of five below the leanest window the model
    // found, which leaves room for a window leaner than any sampled without
    // leaving room for a runner that has stopped delivering.
    //
    // What this floor is *not* is evidence that the oracles can fail. Nothing
    // proportional could be: it says the runner ran. That the oracles have
    // teeth is shown exactly once, deterministically, by
    // `oracles_catch_an_unfenced_coordinator` in `turmoil_ownership.rs`.
    let floor = (end - start) / 16;
    println!(
        "searched seeds {start}..{end}: {writes} writes accepted \
         ({corpus_writes} more from the committed corpus, not counted)"
    );
    assert!(
        writes as u64 > floor,
        "the scenarios must actually reach the fence; saw {writes} accepted \
         writes over seeds {start}..{end}, wanted more than {floor}",
    );

    // Reported rather than asserted on, because it is a measurement of the
    // simulator rather than a property of the protocol. `writes_failed` is
    // turmoil telling a sender there is no route, which a real network does not
    // do; `writes_timed_out` is a request that was accepted for delivery and
    // never answered, which is the shape the node's deadline exists for. If
    // that second number is persistently zero, the deadline is covering a case
    // this search does not reach, and whoever next touches `RPC_TIMEOUT` should
    // know that rather than infer it.
    println!(
        "nodes sent {} writes: {} unanswered at the deadline, {} with no route",
        totals.writes_sent, totals.writes_timed_out, totals.writes_failed
    );
}
