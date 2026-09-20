//! Named ownership stories, run over the same simulated network.
//!
//! `turmoil_scenarios.rs` searches blind: it counts seeds upwards and asks
//! only whether anything broke. That finds orderings nobody would have written
//! down, and it is completely unable to say whether a scenario reached the
//! interesting state at all — an empty run satisfies every oracle.
//!
//! These are the other half. Each one is a specific story with a specific
//! expected ending, spelled out as an action list, and each asserts on the
//! coordinator's audit log rather than only on the invariants. Between them:
//! the search says "nothing broke anywhere", these say "and this particular
//! thing happened".
//!
//! The headline is [`a_returning_owner_is_fenced`], which is the scenario the
//! whole model exists for — node A owns the actor, vanishes, the coordinator
//! hands it to B, and A comes back still holding a guard that says yes.

#[path = "scenario_body/mod.rs"]
mod body;

use body::{check_invariants, run_scenario_logged, run_scenario_unfenced, Action, Event, Scenario};

/// Every story runs on the same network schedule, because the story is in the
/// actions and pinning the seed keeps the two independent. A story that only
/// held on one schedule would be a finding, not a test — and the seed walk is
/// what goes looking for those.
const STORY_SEED: u64 = 0x0D15_EA5E;

fn story(actions: Vec<Action>) -> Scenario {
    Scenario { seed: STORY_SEED, actions }
}

/// The accepted writes, in order, as `(node, epoch)`.
fn accepted(log: &[Event]) -> Vec<(u64, u64)> {
    log.iter()
        .filter_map(|e| match e {
            Event::Wrote { node, epoch, .. } => Some((*node, *epoch)),
            _ => None,
        })
        .collect()
}

/// The refusals, in order, as `(node, epoch)`.
fn fenced(log: &[Event]) -> Vec<(u64, u64)> {
    log.iter()
        .filter_map(|e| match e {
            Event::Fenced { node, epoch } => Some((*node, *epoch)),
            _ => None,
        })
        .collect()
}

/// Long enough for a request that is being swallowed by a partition to give up
/// on. Two of these clear the node's RPC deadline with room to spare.
fn wait() -> Action {
    Action::Sleep { millis: 250 }
}

// ---------------------------------------------------------------------------
// The headline
// ---------------------------------------------------------------------------

/// A owns the actor, is cut off, the coordinator gives it to B, and A returns.
///
/// This is the scenario the epoch is for. When A comes back it still holds
/// `FenceGuard::new(0, 41)`, and that guard still says yes — `src/exec.rs` is
/// explicit that a node cannot fence itself, and here that is not a caveat in
/// a doc comment but an observable fact: A sends the write. What stops it is
/// the coordinator, checking the write against authoritative state at the
/// point where the effect would land.
///
/// The assertion that matters is the last one: epoch 41 has no accepted write
/// after epoch 42 has one. That is `theorem_exclusive_mutable_ownership` and
/// the epoch monotonicity claim, observed rather than proved.
#[test]
fn a_returning_owner_is_fenced() {
    let log: Vec<Event> = run_scenario_logged(story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        Action::Write { node: 0 },
        // A vanishes. From outside, indistinguishable from a crash: its
        // requests stop arriving and nothing says why.
        Action::Isolate { node: 0 },
        // The coordinator does not wait to find out. `tr_revoke_owner` fires
        // against an owner that may well be healthy — unreliable failure
        // detection is modelled, not assumed away.
        Action::Force { next: 1 },
        Action::Poll { node: 1 },
        Action::Acquire { node: 1 },
        Action::Write { node: 1 },
        // A, still cut off, tries to write. The request is dropped, so the
        // coordinator never even sees it.
        Action::Write { node: 0 },
        wait(),
        wait(),
        // A comes back, still holding what it had. `tr_recover`.
        Action::Rejoin { node: 0 },
        Action::Write { node: 0 },
        wait(),
    ]))
    .expect("the returning-owner story must hold its invariants");

    assert!(
        log.contains(&Event::EpochBurned {
            from_epoch: 41,
            to_epoch: 42,
            next: 1,
            forced: true
        }),
        "the coordinator must have burned epoch 41 without A's agreement: {log:?}"
    );

    // A's guard said yes, so A sent the write, so the coordinator refused it.
    // All three are the point.
    assert!(
        fenced(&log).contains(&(0, 41)),
        "the returning owner must have been refused at its stale epoch: {log:?}"
    );

    assert_eq!(
        accepted(&log),
        vec![(0, 41), (1, 42)],
        "A writes at 41, B writes at 42, and nothing else is accepted: {log:?}"
    );
}

// ---------------------------------------------------------------------------
// Cooperative handover
// ---------------------------------------------------------------------------

/// A hands over willingly, and is fenced from the moment it agrees.
///
/// The interesting part is the gap: `tr_begin_transfer` burns the epoch when
/// the owner *agrees*, not when it acknowledges. So between "yes, take it" and
/// "I have stopped", the outgoing owner is already fenced — and this story
/// puts a write in that gap to show it. A protocol that burned the epoch on
/// acknowledgement instead would accept that write, and there would be an
/// interval in which two nodes each believed they could mutate.
#[test]
fn a_cooperative_handover_fences_before_the_release() {
    let log: Vec<Event> = run_scenario_logged(story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        Action::Write { node: 0 },
        // `tr_begin_transfer`. The epoch is burned here.
        Action::Handover { to: 1 },
        // ... and this write is inside the gap: A has agreed but has not yet
        // said it has stopped, and its guard is still (0, 41).
        Action::Write { node: 0 },
        // Only now does A hear that it is revoked, and acknowledge.
        Action::Poll { node: 0 },
        Action::Release { node: 0 },
        Action::Poll { node: 1 },
        Action::Acquire { node: 1 },
        Action::Write { node: 1 },
        // A has released; it has no guard left, so it does not even ask.
        Action::Write { node: 0 },
        wait(),
    ]))
    .expect("the handover story must hold its invariants");

    assert!(
        log.contains(&Event::EpochBurned {
            from_epoch: 41,
            to_epoch: 42,
            next: 1,
            forced: false
        }),
        "agreeing to hand over must burn the epoch: {log:?}"
    );
    assert!(
        fenced(&log).contains(&(0, 41)),
        "the outgoing owner must be fenced from the moment it agrees, not from \
         the moment it acknowledges: {log:?}"
    );
    assert!(
        log.contains(&Event::Released { node: 0, new_epoch: 42 }),
        "the outgoing owner must have acknowledged: {log:?}"
    );
    assert_eq!(
        accepted(&log),
        vec![(0, 41), (1, 42)],
        "one write per owner, each at its own epoch: {log:?}"
    );
}

/// A release that arrives after the coordinator has already given up on it
/// changes nothing.
///
/// A handover starts, the coordinator loses patience and forces the epoch
/// forward anyway, and *then* the outgoing owner's acknowledgement lands. The
/// registry has moved on: the release is refused, no `Released` is recorded,
/// and the node that the interrupted handover was aimed at never gets the
/// actor. Node 2, the one the forced revoke named, does.
///
/// This is the only story that reaches the forced-revoke-from-`Transferring`
/// branch, which is the one place the implementation burns an epoch that was
/// itself already a burn target.
#[test]
fn a_late_release_cannot_resurrect_a_superseded_transfer() {
    let log: Vec<Event> = run_scenario_logged(story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        Action::Write { node: 0 },
        Action::Handover { to: 1 },
        // A learns it is revoked, but does not acknowledge yet.
        Action::Poll { node: 0 },
        // The coordinator gives up on the handover and burns again.
        Action::Force { next: 2 },
        // A's acknowledgement, too late to mean anything.
        Action::Release { node: 0 },
        Action::Poll { node: 2 },
        Action::Acquire { node: 2 },
        Action::Write { node: 2 },
        // A gave the actor up, so it has no guard and sends nothing.
        Action::Write { node: 0 },
        wait(),
    ]))
    .expect("the interrupted-handover story must hold its invariants");

    let burns: Vec<(u64, u64, u64, bool)> = log
        .iter()
        .filter_map(|e| match e {
            Event::EpochBurned { from_epoch, to_epoch, next, forced } => {
                Some((*from_epoch, *to_epoch, *next, *forced))
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        burns,
        vec![(41, 42, 1, false), (42, 43, 2, true)],
        "the cooperative burn, then the forced one on top of it: {log:?}"
    );
    assert!(
        !log.iter().any(|e| matches!(e, Event::Released { .. })),
        "the release arrived after the transfer it belonged to was superseded, \
         so it must have been refused: {log:?}"
    );
    assert_eq!(
        accepted(&log),
        vec![(0, 41), (2, 43)],
        "node 1 was named by a transfer that never completed and must never \
         have written; epoch 42 belongs to nobody: {log:?}"
    );
}

// ---------------------------------------------------------------------------
// What silence is, and is not
// ---------------------------------------------------------------------------

/// An isolated owner does not get refused. It gets nothing at all.
///
/// Worth stating separately because the two are easy to conflate and the
/// protocol depends on the difference. A partition is silence: the request
/// never reaches the coordinator, so the coordinator never decides anything,
/// so there is no `Fenced` in the log. The owner meanwhile is still the owner
/// — nothing has revoked it — and a node that treated its own timeout as a
/// refusal, or as permission to stand down, would be inventing a decision
/// nobody made.
///
/// The write after the repair is what stops this story asserting nothing. The
/// two claims below — one acceptance before the partition, no refusals — are
/// both satisfied by a node that simply never tried, and the coordinator's log
/// cannot tell the difference, because not seeing a request is exactly what
/// being partitioned from one looks like. So the story ends by healing the
/// network and writing again: that write is accepted at the *same* epoch, which
/// says the node still held its guard and was still willing to use it through
/// the whole isolation. The silence in the middle was the network's, not the
/// node's.
#[test]
fn an_isolated_owner_is_met_with_silence_not_refusal() {
    let log: Vec<Event> = run_scenario_logged(story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        Action::Write { node: 0 },
        Action::Isolate { node: 0 },
        Action::Write { node: 0 },
        wait(),
        wait(),
        Action::Write { node: 0 },
        wait(),
        wait(),
        // Both of those have given up by now — two deadlines have passed — so
        // the write below is a fresh request rather than one of them arriving
        // late.
        Action::Rejoin { node: 0 },
        Action::Write { node: 0 },
        wait(),
    ]))
    .expect("the isolation story must hold its invariants");

    assert_eq!(
        accepted(&log),
        vec![(0, 41), (0, 41)],
        "one write before the partition and one after it heals, both at the \
         epoch this node never stopped owning; the two in between reached \
         nobody: {log:?}"
    );
    assert!(
        fenced(&log).is_empty(),
        "a dropped request is not a refusal; the coordinator never saw these: \
         {log:?}"
    );
}

/// A node with no grant never asks for anything.
///
/// The executable side of P8 — no authority without a capability. Node 1 is
/// not the intended owner at the start, so its poll comes back empty, so it
/// has no guard, so its acquire and its write are never sent. The coordinator
/// does not have to refuse them, because a node that has been given nothing
/// has nothing to present.
#[test]
fn a_node_with_no_grant_sends_nothing() {
    let log: Vec<Event> = run_scenario_logged(story(vec![
        Action::Poll { node: 1 },
        Action::Acquire { node: 1 },
        Action::Write { node: 1 },
        wait(),
    ]))
    .expect("the ungranted-node story must hold its invariants");

    assert!(
        log.is_empty(),
        "a node that was offered nothing must not have reached the registry at \
         all: {log:?}"
    );
}

// ---------------------------------------------------------------------------
// The oracles, tested
// ---------------------------------------------------------------------------

/// The story the self-test below runs twice: once fenced, once not.
///
/// A owns epoch 41 and writes. The coordinator burns the epoch to 42 and B
/// takes it. A — never partitioned, simply out of date — writes again with the
/// guard it still holds.
fn stale_owner_story() -> Scenario {
    story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        Action::Write { node: 0 },
        Action::Force { next: 1 },
        Action::Poll { node: 1 },
        Action::Acquire { node: 1 },
        Action::Write { node: 1 },
        // A's guard is (0, 41) and says yes. Only the registry knows better.
        Action::Write { node: 0 },
        wait(),
    ])
}

/// With the fence in place, the stale write is refused.
#[test]
fn a_forced_revoke_fences_a_healthy_owner() {
    let log: Vec<Event> = run_scenario_logged(stale_owner_story())
        .expect("the stale-owner story must hold its invariants");

    assert!(
        fenced(&log).contains(&(0, 41)),
        "a revoked owner that never noticed must still be refused: {log:?}"
    );
    assert_eq!(
        accepted(&log),
        vec![(0, 41), (1, 42)],
        "the stale write must not have been accepted: {log:?}"
    );
}

/// Without it, the oracles catch it.
///
/// This is the question every oracle has to answer about itself: would it
/// notice? A suite that cannot fail is indistinguishable from one that passes,
/// and a green run that only shows the assertions did not fire is very weak
/// evidence. So the *same* story runs again with one bit changed — the
/// coordinator stops checking writes against the registry — and the oracles
/// are required to reject the result.
///
/// The bit is the fence and nothing else: same actions, same seed, same
/// network, same oracles. What separates the two runs is exactly the check
/// that `src/exec.rs` says has to happen where the effect lands.
#[test]
fn oracles_catch_an_unfenced_coordinator() {
    let log: Vec<Event> = run_scenario_unfenced(stale_owner_story())
        .expect("the unfenced run is still a run; it must complete");

    // Sanity first: the run has to have reached the interesting state, or the
    // rejection below would be about something else entirely.
    assert_eq!(
        accepted(&log),
        vec![(0, 41), (1, 42), (0, 41)],
        "without the fence the stale write must have been accepted, which is \
         the thing the oracles are supposed to catch: {log:?}"
    );

    let verdict = check_invariants(&log);
    let Err(message) = verdict else {
        panic!(
            "the oracles accepted a log containing a write at a superseded \
             epoch, so they would not have caught it in any other test either: \
             {log:?}"
        );
    };
    assert!(
        message.contains("P5/P6"),
        "expected the superseded-epoch oracle to be the one that fired, got: \
         {message}"
    );
    println!("oracles rejected the unfenced run: {message}");
}
