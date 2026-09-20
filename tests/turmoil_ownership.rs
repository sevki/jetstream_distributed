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

use body::{
    check_invariants, run_scenario_logged, run_scenario_probed, run_scenario_unfenced, Action,
    Event, Scenario,
};

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
        // `tr_begin_transfer`. A is the one agreeing, so A is the one sending
        // it, and the epoch is burned here.
        Action::Handover { from: 0, to: 1 },
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

/// An interrupted transfer goes back where it came from, and a late release
/// cannot resurrect it.
///
/// A handover starts, the coordinator loses patience and forces the epoch
/// forward anyway, and *then* the outgoing owner's acknowledgement lands. Two
/// things have to hold. The release is refused, because the registry has moved
/// on. And the actor comes back to A — not to node 2, which is what the
/// `FORCE` names.
///
/// That second one is the whole reason this story exists. `tr_revoke_owner`
/// matches `Owned` only; the model's sole recovery from `Transferring` is
/// `tr_abort_transfer`, which burns another epoch and offers the actor back to
/// `from`. A coordinator that instead honoured the caller's choice of
/// successor here would be taking a step the transition relation does not
/// contain, and every oracle it satisfied afterwards would be evidence about a
/// machine nobody proved anything about. So the `next: 2` below is passed and
/// deliberately ignored, and this asserts that it was.
#[test]
fn an_interrupted_transfer_returns_to_the_node_it_came_from() {
    let log: Vec<Event> = run_scenario_logged(story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        Action::Write { node: 0 },
        Action::Handover { from: 0, to: 1 },
        // A learns it is revoked, but does not acknowledge yet.
        Action::Poll { node: 0 },
        // The coordinator gives up on the handover. `tr_abort_transfer`, and
        // `next` has no say in where the actor lands.
        Action::Force { next: 2 },
        // A's acknowledgement, too late to mean anything.
        Action::Release { node: 0 },
        // A takes the actor back at the epoch the abort offered it.
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
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
        vec![(41, 42, 1, false), (42, 43, 0, true)],
        "the cooperative burn, then the abort on top of it — and the abort \
         offers the actor back to node 0, whatever the caller asked for: \
         {log:?}"
    );
    assert!(
        !log.iter().any(|e| matches!(e, Event::Released { .. })),
        "the release arrived after the transfer it belonged to was superseded, \
         so it must have been refused: {log:?}"
    );
    assert_eq!(
        accepted(&log),
        vec![(0, 41), (0, 43)],
        "node 1 was named by a transfer that never completed and node 2 by an \
         abort that does not honour it, so neither may ever have written; \
         epoch 42 belongs to nobody: {log:?}"
    );
}

/// Only the owner can agree to hand the actor over.
///
/// `tr_begin_transfer` is an action by `from`, and the registry checks the
/// sender, so a `BEGIN` from a node that does not hold the actor changes
/// nothing. Without that check the coordinator would accept an agreement on
/// behalf of a node that never gave one — and since the request is sent by the
/// node rather than around it, a partitioned owner cannot agree either, which
/// is the simulation's counterpart of the liveness guard the model carries.
#[test]
fn a_non_owner_cannot_agree_to_hand_over() {
    let log: Vec<Event> = run_scenario_logged(story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        Action::Write { node: 0 },
        // Node 1 does not hold the actor and says so anyway.
        Action::Handover { from: 1, to: 2 },
        // Node 0 is untouched: still the owner, still at 41.
        Action::Write { node: 0 },
        wait(),
    ]))
    .expect("the impostor-handover story must hold its invariants");

    assert!(
        !log.iter().any(|e| matches!(e, Event::EpochBurned { .. })),
        "a `BEGIN` from a node that is not the owner must not burn anything: \
         {log:?}"
    );
    assert_eq!(
        accepted(&log),
        vec![(0, 41), (0, 41)],
        "the real owner keeps writing at its own epoch throughout: {log:?}"
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
/// Two things stop this story asserting nothing. The claims below — one
/// acceptance before the partition, no refusals — are both satisfied by a node
/// that simply never tried, and the coordinator's log cannot tell the
/// difference, because not seeing a request is exactly what being partitioned
/// from one looks like.
///
/// So the node is asked directly: four writes sent, two of them unanswered.
/// That is the claim, stated where it is observable. And the story ends by
/// healing the network and writing once more at the *same* epoch, which says
/// the node still held its guard and was still the owner throughout. The
/// silence in the middle was the network's, not the node's.
#[test]
fn an_isolated_owner_is_met_with_silence_not_refusal() {
    let (log, attempts) = run_scenario_probed(story(vec![
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
        attempts[0].writes_sent, 4,
        "the node must have sent all four writes — one before the partition, \
         two into it and one after the repair. Fewer means the assertions \
         below are about a node that stopped trying, not about a network that \
         stopped delivering: {attempts:?}"
    );
    assert_eq!(
        attempts[0].writes_timed_out, 2,
        "exactly the two writes sent while isolated must have gone unanswered: \
         {attempts:?}"
    );

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

/// A stale write with nothing after it, which is what the first version of the
/// oracles could not see.
fn burned_epoch_story() -> Scenario {
    story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        Action::Write { node: 0 },
        // The epoch is burned. Node 1 is offered the actor and never takes it,
        // so no later write exists to compare node 0's next one against.
        Action::Force { next: 1 },
        Action::Write { node: 0 },
        wait(),
    ])
}

/// The oracles catch a stale write even when nobody writes after it.
///
/// This is the case the fencing oracle was added for. Comparing writes against
/// writes only notices a stale one once the replacement owner has written too;
/// here nobody does, so `Wrote(0, 41)` after a burn to 42 has one writer per
/// epoch, a strictly increasing burn and an acquire behind it. Every check the
/// first version of `check_invariants` made passed on this log.
#[test]
fn oracles_catch_a_write_at_a_burned_epoch() {
    let log: Vec<Event> = run_scenario_unfenced(burned_epoch_story())
        .expect("the unfenced run is still a run; it must complete");

    assert_eq!(
        accepted(&log),
        vec![(0, 41), (0, 41)],
        "without the fence the write at the burned epoch must have been \
         accepted, and nothing may follow it: {log:?}"
    );

    let Err(message) = check_invariants(&log) else {
        panic!(
            "the oracles accepted a write at an epoch the registry had already \
             burned past, which is the failure this whole model exists to rule \
             out: {log:?}"
        );
    };
    assert!(
        message.contains("claims 2/3"),
        "expected the fencing oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the burned-epoch run: {message}");
}

/// And with the fence in place, the same story is refused rather than accepted.
#[test]
fn a_write_at_a_burned_epoch_is_refused() {
    let log: Vec<Event> = run_scenario_logged(burned_epoch_story())
        .expect("the burned-epoch story must hold its invariants");

    assert!(
        fenced(&log).contains(&(0, 41)),
        "the write at the burned epoch must have been refused: {log:?}"
    );
    assert_eq!(
        accepted(&log),
        vec![(0, 41)],
        "only the write made while node 0 really owned epoch 41: {log:?}"
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
