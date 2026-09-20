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
    Coord, Event, Scenario, INITIAL_EPOCH,
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
/// So the node is asked directly: four writes sent, two of which never reached
/// anybody. And the story ends by healing the network and writing once more at
/// the *same* epoch, which says the node still held its guard and was still the
/// owner throughout.
///
/// **Where turmoil is kinder than a network.** The two failed writes are
/// `writes_failed`, not `writes_timed_out`, and that is a fact about the
/// simulator rather than about partitions. A real partition drops the SYN and
/// the sender learns nothing until its own deadline expires; turmoil knows
/// there is no route and says so immediately. This assertion is written the way
/// the run actually came out rather than the way a network would behave,
/// because a test that asserts the tidier thing is asserting something false.
///
/// It costs nothing here, and it is worth being precise about why. A node that
/// can distinguish "no route" from "no reply" holds information a real one does
/// not, and a protocol that used it would be leaning on the simulator. This one
/// cannot: `run_cmd` counts both and acts on neither, because a node that
/// treated either as a decision about ownership would be inventing one nobody
/// made. What the coordinator saw — nothing — is the same under both.
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
        attempts[0].writes_failed, 2,
        "exactly the two writes sent while isolated must have failed to reach \
         the coordinator, which is how turmoil reports having no route: \
         {attempts:?}"
    );
    assert_eq!(
        attempts[0].writes_timed_out, 0,
        "and none may have expired on the deadline — see the note above: a \
         partition already in place when the request is made is reported at \
         once here, so a timeout in this story would mean something other than \
         the partition happened: {attempts:?}"
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

/// A held request expires on the node's deadline, and the node carries on.
///
/// The other half of what a network can do to a request, and the half the
/// partition stories cannot reach. `Isolate` removes the route, which turmoil
/// reports to the sender at once; `Stall` holds the messages, so the request is
/// accepted for delivery and simply never answered. That second shape is what
/// `RPC_TIMEOUT` exists for, and until this story existed nothing exercised it
/// — the seed walk reported 284 writes sent across 256 seeds with *zero*
/// unanswered at the deadline, which is a deadline that had never once fired.
///
/// What the node may not do is conclude anything. A timeout says the node got
/// no answer; it does not say the write was not applied, and the held request
/// may well land later. So the assertion here is about the node giving up and
/// then continuing to work, not about what the registry did with the request it
/// was still holding.
#[test]
fn a_held_request_expires_and_the_node_carries_on() {
    let (log, attempts) = run_scenario_probed(story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        // The route stays up. The messages just stop moving.
        Action::Stall { node: 0 },
        Action::Write { node: 0 },
        // Two deadlines' worth, so the node has certainly given up.
        wait(),
        wait(),
        Action::Resume { node: 0 },
        // ... and it is still working: this one goes through normally.
        Action::Write { node: 0 },
        wait(),
    ]))
    .expect("the held-request story must hold its invariants");

    assert_eq!(
        attempts[0].writes_sent, 2,
        "both writes must have been sent — the node does not stop trying \
         because one went unanswered: {attempts:?}"
    );
    assert_eq!(
        attempts[0].writes_timed_out, 1,
        "the held write must have spent its whole deadline unanswered, which \
         is the case `Isolate` cannot produce: {attempts:?}"
    );
    assert_eq!(
        attempts[0].writes_failed, 0,
        "and nothing may have failed outright: the route was never removed, \
         only stalled: {attempts:?}"
    );

    // Deliberately not pinned to a count. Whether the held request reaches the
    // coordinator once the hold is released depends on whether the payload
    // survives a sender that has already abandoned the connection — a property
    // of the simulator, not of this protocol. What must hold either way is that
    // nothing was accepted from anyone else, at any other epoch.
    //
    // Which means this story alone cannot show that a delayed request is ever
    // delivered late at all: everything it asserts is satisfied by the ordinary
    // write after `Resume`. That gap is covered deliberately rather than left
    // open — `a_delayed_write_arrives_at_a_registry_that_moved_on` releases the
    // hold while the node is still waiting, so the delivery is observable, and
    // `a_timeout_is_not_evidence_the_write_did_not_land` covers the case where
    // the request lands and the *answer* is what goes missing.
    let writes = accepted(&log);
    assert!(
        !writes.is_empty() && writes.iter().all(|w| *w == (0, 41)),
        "every accepted write must be node 0 at epoch 41, the epoch it never \
         stopped owning, and there must be at least the one sent after the \
         hold was released: {log:?}"
    );
}

/// A request that sits in the network arrives at a registry that has moved on,
/// and is fenced.
///
/// This is the claim the seed walk could not reach and the held-request story
/// above does not make: *arbitrarily delayed requests are safe*. The write is
/// held on the wire — not dropped, not refused — while the coordinator burns
/// the epoch underneath it, and it is delivered afterwards. Nothing about the
/// request has changed; the world it arrives in has.
///
/// The hold is released well inside the node's deadline on purpose, so the
/// request is delivered to a coordinator the node is still waiting on. That is
/// what makes the refusal observable: had the node given up first, the write
/// would have been fenced with nobody listening, and the assertion below could
/// not tell that from a request that was never delivered at all.
#[test]
fn a_delayed_write_arrives_at_a_registry_that_moved_on() {
    let (log, attempts) = run_scenario_probed(story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        Action::Write { node: 0 },
        // The route stays up; this write stops on the wire.
        Action::Stall { node: 0 },
        Action::Write { node: 0 },
        // ... and while it is sitting there, the registry moves on without it.
        Action::Force { next: 1 },
        // Delivered now, into a world that has changed.
        Action::Resume { node: 0 },
        wait(),
    ]))
    .expect("the delayed-write story must hold its invariants");

    assert_eq!(
        attempts[0].writes_sent, 2,
        "both writes must have been sent: {attempts:?}"
    );
    assert_eq!(
        attempts[0].writes_timed_out, 0,
        "the held write must have been answered before the node gave up — the          point of this story is a delivered request meeting a changed registry,          and a timeout here would mean it was never delivered: {attempts:?}"
    );
    assert!(
        fenced(&log).contains(&(0, 41)),
        "the delayed write must have been refused on arrival, at an epoch the          registry had already burned past: {log:?}"
    );
    assert_eq!(
        accepted(&log),
        vec![(0, 41)],
        "only the write made before the epoch moved: {log:?}"
    );
}

/// A write can land and the node still not know it.
///
/// The other direction, and the one no amount of network behaviour produces:
/// the coordinator applies the write and answers after the caller has given up.
/// `rpc`'s doc comment says a node that read "no reply" as "not applied" would
/// be the bug this whole model is about; this is that sentence as an assertion.
///
/// Both writes are accepted, including the one the node counts as timed out.
#[test]
fn a_timeout_is_not_evidence_the_write_did_not_land() {
    let (log, attempts) = run_scenario_probed(story(vec![
        Action::Poll { node: 0 },
        Action::Acquire { node: 0 },
        // The registry will apply the next request and answer far too late.
        Action::SlowReply,
        Action::Write { node: 0 },
        wait(),
        wait(),
        // The node has given up on that one, and carries on.
        Action::Write { node: 0 },
        wait(),
    ]))
    .expect("the late-reply story must hold its invariants");

    assert_eq!(
        attempts[0].writes_timed_out, 1,
        "the node must have given up on the first write: {attempts:?}"
    );
    assert_eq!(
        accepted(&log),
        vec![(0, 41), (0, 41)],
        "and both must have been accepted — the one it gave up on landed, which          is precisely why a node may not read its own timeout as a verdict:          {log:?}"
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
///
/// It expects the same oracle as `oracles_catch_an_unfenced_coordinator`, and
/// that is not a redundancy: both are fencing failures and both should say so.
/// What differs is the run. There a replacement owner writes first, so the
/// write-against-write comparison could see it; here nobody does, and only a
/// burn-driven high-water mark can.
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

// ---------------------------------------------------------------------------
// The line protocol, checked against the model's preconditions
// ---------------------------------------------------------------------------

/// The registry refuses a successor that is not a node.
///
/// `tr_begin_transfer` and `tr_revoke_owner` both require
/// `pre.nodes.contains(to)`. Nothing in the simulation sends an unknown
/// successor — the driver takes its argument modulo `NODES` — and that is
/// exactly why this is worth asserting at the registry rather than trusting the
/// caller. A precondition the caller happens to satisfy is not a precondition
/// the registry enforces, and the request arrives over a socket.
///
/// Driven against `Coord` directly, with raw lines, because the action alphabet
/// cannot express a malformed request.
#[test]
fn the_registry_refuses_a_successor_that_is_not_a_node() {
    let mut coord = Coord::new(true);
    assert_eq!(coord.handle("POLL 0"), format!("GRANT {INITIAL_EPOCH}"));
    assert_eq!(coord.handle(&format!("ACQUIRE 0 {INITIAL_EPOCH}")), "OK");

    assert_eq!(
        coord.handle("BEGIN 0 99"),
        "NO",
        "a handover to a node that does not exist must be refused"
    );
    assert_eq!(
        coord.handle("FORCE 99"),
        "NO",
        "a forced revoke naming a node that does not exist must be refused"
    );

    // ... and the registry is untouched by either: node 0 still owns it.
    assert_eq!(coord.handle(&format!("WRITE 0 {INITIAL_EPOCH}")), "OK 1");
}

/// The registry refuses an acquire that quotes the wrong epoch.
///
/// `tr_acquire` wants a `Grant` for exactly the epoch being taken, and `ACQUIRE`
/// guards it with `e == *epoch`. I listed this guard as one the oracles could
/// not witness and left it at that — which was half an answer. An oracle cannot
/// see it, because the handler logs the epoch it *acquired* and the request's
/// epoch is never recorded, so `POLL 0` then `ACQUIRE 0 999` produces a
/// perfectly valid-looking `Acquired(0, 41)`. A protocol test can see it, and I
/// had already built the means and not used it.
#[test]
fn the_registry_refuses_an_acquire_quoting_the_wrong_epoch() {
    let mut coord = Coord::new(true);
    assert_eq!(coord.handle("POLL 0"), format!("GRANT {INITIAL_EPOCH}"));

    assert_eq!(
        coord.handle("ACQUIRE 0 999"),
        "NO",
        "an acquire must name the epoch it is being offered, not any epoch"
    );

    // The actor is untaken, so the right request still works — which is what
    // makes the refusal about the epoch rather than about the state.
    assert_eq!(coord.handle(&format!("ACQUIRE 0 {INITIAL_EPOCH}")), "OK");
}

/// The registry does not offer the actor to a node it is not holding it for.
///
/// `Granted` has exactly the flaw that made `Revoked` decorative: it is logged
/// *inside* `POLL`'s `intended == node` arm, so deleting that guard moves the
/// logging with it and the oracle sees an empty log rather than a bad offer.
/// The oracle-side check is still worth having — it rejects a bad offer in a
/// hand-built log — but it cannot witness the coordinator's decision, and only
/// the protocol boundary can.
///
/// Found by writing the generalisation out for the `Revoked` case rather than
/// by being told, which is the first time this pattern has been caught one step
/// ahead of the review instead of one behind.
#[test]
fn the_registry_does_not_offer_the_actor_to_a_bystander() {
    let mut coord = Coord::new(true);

    // The actor starts offered to node 0 and to nobody else.
    assert_eq!(
        coord.handle("POLL 1"),
        "NONE",
        "the actor is held for node 0; node 1 must be offered nothing"
    );
    assert_eq!(
        coord.handle("POLL 2"),
        "NONE",
        "nor node 2"
    );
    assert_eq!(coord.handle("POLL 0"), format!("GRANT {INITIAL_EPOCH}"));

    // And the same once it has moved on: a forced revoke to node 1 leaves the
    // others with nothing.
    assert_eq!(coord.handle(&format!("ACQUIRE 0 {INITIAL_EPOCH}")), "OK");
    assert_eq!(coord.handle("FORCE 1"), "OK");
    assert_eq!(
        coord.handle("POLL 0"),
        "NONE",
        "the node that just lost the actor is offered nothing"
    );
    assert_eq!(coord.handle("POLL 1"), format!("GRANT {}", INITIAL_EPOCH + 1));
}

/// The registry does not tell a bystander to stand down.
///
/// `Message::Revoke` binds its `target` to the outgoing owner, and `POLL`
/// guards it with `from == node` on the `Transferring` branch. Logging the
/// revoke was not enough to witness that guard, and the reason is worth
/// writing down: the log line sits *inside* the guarded arm, so deleting the
/// guard moves the logging with it. An audit event can only witness a guard it
/// is not nested in.
#[test]
fn the_registry_does_not_tell_a_bystander_to_stand_down() {
    let mut coord = Coord::new(true);
    assert_eq!(coord.handle("POLL 0"), format!("GRANT {INITIAL_EPOCH}"));
    assert_eq!(coord.handle(&format!("ACQUIRE 0 {INITIAL_EPOCH}")), "OK");
    assert_eq!(coord.handle("BEGIN 0 1"), "OK");

    // The actor is being taken from node 0. Nobody else is standing down.
    assert_eq!(
        coord.handle("POLL 2"),
        "NONE",
        "a node outside the transfer must not be told to stand down"
    );
    assert_eq!(
        coord.handle("POLL 1"),
        "NONE",
        "nor must the node the actor is being handed to — it is offered the \
         actor once the release lands, not revoked"
    );

    // The outgoing owner is.
    assert_eq!(coord.handle("POLL 0"), format!("REVOKE {}", INITIAL_EPOCH + 1));
}

/// A release is an acknowledgement of one transfer, not of whichever is current.
///
/// `tr_complete_release` requires `Message::Released { from, new_epoch }` to
/// name the transfer's *current* `new_epoch`. Without the epoch on the wire,
/// a release that node 0 sent for an earlier handover — delayed, or replayed —
/// completes a later one, because the only thing distinguishing them is the
/// epoch.
///
/// The replay here is the request arriving twice, which the model treats as
/// something the network may always do.
#[test]
fn a_release_for_an_earlier_transfer_does_not_complete_a_later_one() {
    let mut coord = Coord::new(true);
    let first = INITIAL_EPOCH;

    // Node 0 takes the actor and agrees to hand it to node 1.
    assert_eq!(coord.handle("POLL 0"), format!("GRANT {first}"));
    assert_eq!(coord.handle(&format!("ACQUIRE 0 {first}")), "OK");
    assert_eq!(coord.handle("BEGIN 0 1"), "OK");
    assert_eq!(coord.handle("POLL 0"), format!("REVOKE {}", first + 1));

    // It acknowledges, and the transfer completes.
    assert_eq!(coord.handle(&format!("RELEASE 0 {}", first + 1)), "OK");

    // Node 0 gets the actor back later, and agrees to hand it on again. This
    // is a different transfer, at a different epoch.
    assert_eq!(coord.handle("FORCE 0"), "OK");
    let second = first + 2;
    assert_eq!(coord.handle("POLL 0"), format!("GRANT {second}"));
    assert_eq!(coord.handle(&format!("ACQUIRE 0 {second}")), "OK");
    assert_eq!(coord.handle("BEGIN 0 2"), "OK");

    // The old acknowledgement arrives again. It names the wrong epoch, and
    // completing the current transfer with it would hand node 2 the actor on
    // the strength of an agreement node 0 gave about node 1.
    assert_eq!(
        coord.handle(&format!("RELEASE 0 {}", first + 1)),
        "NO",
        "a replayed release naming an old epoch must not complete this transfer"
    );

    // The current one still works, which is what makes the refusal above about
    // the epoch rather than about the state.
    assert_eq!(coord.handle(&format!("RELEASE 0 {}", second + 1)), "OK");
}

/// Two nodes writing at one epoch is rejected — claim 1, with a witness.
///
/// The last of the audit. Claim 1 reads *writes* where the theorem it names is
/// about *ownership*, which is the shape of the P5/P6 bug, and the argument
/// that the acquire check covers the ownership half is the same kind of
/// argument that failed twice in this file's history. So it gets a witness
/// instead of an argument: a log this oracle, specifically, rejects.
#[test]
fn oracles_reject_two_writers_at_one_epoch() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::Wrote { node: 0, epoch: 41, seq: 1 },
        Event::Wrote { node: 1, epoch: 41, seq: 2 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!("the oracles accepted two nodes writing at one epoch: {log:?}");
    };
    assert!(
        message.contains("claim 1"),
        "expected the exclusivity oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the shared epoch: {message}");
}

/// One node writing twice at one epoch is fine.
///
/// The paired accept for claim 1, and the reason it is worth writing down: the
/// rejection above differs from this log in exactly one field. Without it,
/// nothing distinguishes "two writers at one epoch" from "two writes at one
/// epoch", and an oracle that had drifted to the second would still pass its
/// own witness while forbidding the ordinary case.
#[test]
fn oracles_accept_one_node_writing_twice_at_one_epoch() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::Wrote { node: 0, epoch: 41, seq: 1 },
        Event::Wrote { node: 0, epoch: 41, seq: 2 },
    ];

    assert!(
        check_invariants(&log).is_ok(),
        "an owner writing more than once at its own epoch is the ordinary case \
         and must be accepted: {log:?}"
    );
}

/// An epoch that moves to a different node *with* a burn is fine.
///
/// The paired accept for the forward half of claim 5, and it differs from that
/// witness by the burn alone — same two acquires, same two epochs, same two
/// nodes. What the oracle objects to is an epoch that moved without being
/// burned, and this is what says so.
#[test]
fn oracles_accept_a_handover_to_another_node_across_a_burn() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 1, forced: true },
        Event::Granted { node: 1, epoch: 42 },
        Event::Acquired { node: 1, epoch: 42 },
        Event::Wrote { node: 1, epoch: 42, seq: 1 },
    ];

    assert!(
        check_invariants(&log).is_ok(),
        "a forced revoke handing the actor to another node is the headline \
         path and must be accepted: {log:?}"
    );
}

/// A node acquiring an epoch it was not offered is rejected.
///
/// `tr_acquire` requires the acquiring node to be the `intended_owner` and a
/// matching `Grant` to be in flight — the grant is the capability. Nothing in
/// the suite correlated the two until this check existed, and the consequence
/// was as blunt as it gets: **deleting the coordinator's `intended == node`
/// guard would have left every test green.** An oracle suite that cannot see a
/// deleted guard is not auditing the thing the guard protects.
#[test]
fn oracles_reject_an_acquire_by_a_node_that_was_not_offered() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 1, forced: true },
        // The actor was offered to node 1. Node 2 takes it.
        Event::Acquired { node: 2, epoch: 42 },
        Event::Wrote { node: 2, epoch: 42, seq: 1 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!(
            "the oracles accepted an acquire by a node the actor was never \
             offered to: {log:?}"
        );
    };
    assert!(
        message.contains("P8 (grant)"),
        "expected the grant oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the uninvited acquire: {message}");
}

/// The same log with the offered node taking it is fine.
///
/// The paired accept, differing from the rejection in the acquiring node
/// alone — `oracles_accept_a_handover_to_another_node_across_a_burn` is
/// literally this log with node 1 in node 2's place, which is why that test
/// serves as this one's pair rather than a third being added.
///
/// A node acquiring at the *initial* epoch is the other case worth pinning,
/// because the oracle has to start from somewhere and taking that from the log
/// would make the first acquire valid by whoever happened to make it.
#[test]
fn oracles_reject_a_first_acquire_by_a_node_that_was_not_offered() {
    let log = vec![Event::Acquired { node: 2, epoch: 41 }];

    let Err(message) = check_invariants(&log) else {
        panic!(
            "the oracles accepted a first acquire by a node the actor was not \
             initially offered to: {log:?}"
        );
    };
    assert!(
        message.contains("P8 (grant)"),
        "expected the grant oracle to be the one that fired, got: {message}"
    );
}

/// An acquire with no offer behind it is rejected.
///
/// `tr_acquire` has two conjuncts and this suite only ever checked one. Being
/// the `intended_owner` is necessary; the model also wants
/// `pre.network.contains(Message::Grant { to: n, epoch })` — the offer must
/// actually have been made. Nothing could check that while grants went
/// unrecorded, so `POLL` now writes a `Granted` to the audit log and this is
/// the other conjunct, checked.
///
/// The gap was mine rather than found: I wrote out both halves of `tr_acquire`
/// in a review reply, implemented the first, and did not notice.
#[test]
fn oracles_reject_an_acquire_with_no_offer_behind_it() {
    let log = vec![
        // Node 0 is the intended owner at 41 and takes it, having never been
        // told it was on offer.
        Event::Acquired { node: 0, epoch: 41 },
        Event::Wrote { node: 0, epoch: 41, seq: 1 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!("the oracles accepted an acquire with no grant behind it: {log:?}");
    };
    assert!(
        message.contains("P8 (grant)"),
        "expected the grant oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the ungranted acquire: {message}");
}

/// The same log with the offer recorded is fine.
///
/// The paired accept, differing by the `Granted` alone.
#[test]
fn oracles_accept_an_acquire_with_its_offer() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::Wrote { node: 0, epoch: 41, seq: 1 },
    ];

    assert!(
        check_invariants(&log).is_ok(),
        "an offer, the offered node taking it, and a write at that epoch is the \
         ordinary path and must be accepted: {log:?}"
    );
}

/// An offer to a node the actor is not being held for is rejected.
///
/// The registry's side of the same conjunct. `POLL` guards this with
/// `intended == node`, and until grants were logged, deleting that guard
/// changed nothing any test could see.
#[test]
fn oracles_reject_an_offer_to_a_node_the_actor_is_not_held_for() {
    let log = vec![Event::Granted { node: 2, epoch: 41 }];

    let Err(message) = check_invariants(&log) else {
        panic!("the oracles accepted an offer to a node with no claim: {log:?}");
    };
    assert!(
        message.contains("P8 (grant)"),
        "expected the grant oracle to be the one that fired, got: {message}"
    );
}

/// An epoch acquired twice is rejected, even by the same node.
///
/// `tr_acquire` matches on `Unowned`, so it cannot fire a second time for an
/// epoch — the actor is already `Owned`. The check here rejected only a
/// *different* node, and I asserted in review that a same-node repeat would be
/// caught by it, which was simply false.
#[test]
fn oracles_reject_an_epoch_acquired_twice_by_one_node() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!("the oracles accepted an epoch being acquired twice: {log:?}");
    };
    assert!(
        message.contains("P5/P6"),
        "expected the ownership oracle to be the one that fired, got: {message}"
    );
}

/// An acquire while a handover is still in flight is rejected.
///
/// The actor is `Transferring` between the agreement and the release, and in
/// that phase the registry offers nothing and nobody acquires. Reading the
/// outgoing owner out of `Acquired` alone — without the phase — let a node that
/// acquired mid-transfer count as a real owner, and a second cooperative burn
/// then overwrote the pending transfer. The whole sequence passed.
///
/// This was the inference I flagged in review as load-bearing and mine. It was
/// also wrong.
#[test]
fn oracles_reject_an_acquire_during_a_handover() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 1, forced: false },
        // Nobody has released yet, so the actor is still `Transferring`.
        Event::Granted { node: 1, epoch: 42 },
        Event::Acquired { node: 1, epoch: 42 },
        Event::EpochBurned { from_epoch: 42, to_epoch: 43, next: 2, forced: false },
        Event::Released { node: 1, new_epoch: 43 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!(
            "the oracles accepted an acquire made while a handover was still \
             in flight: {log:?}"
        );
    };
    assert!(
        message.contains("claim 4"),
        "expected the transfer oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the mid-transfer acquire: {message}");
}

/// A node handing the actor to itself is rejected.
///
/// `tr_begin_transfer` requires `from != to`. The coordinator guards it, and
/// until this check existed deleting that guard changed nothing any test could
/// see — the log records a well-formed burn either way.
#[test]
fn oracles_reject_a_node_handing_the_actor_to_itself() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 0, forced: false },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!("the oracles accepted a handover from a node to itself: {log:?}");
    };
    assert!(
        message.contains("claim 4"),
        "expected the transfer oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the self-handover: {message}");
}

/// A stand-down order aimed at a node outside the transfer is rejected.
///
/// `Message::Revoke` binds its `target` to the transfer's outgoing owner, and
/// `POLL` guards that with `from == node` on the `Transferring` branch. Until
/// revokes were logged that guard was invisible: the registry could tell any
/// node to stand down and no test would know. This was one of the two guards I
/// listed as still unwitnessed; the other is below.
#[test]
fn oracles_reject_a_stand_down_aimed_outside_the_transfer() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 1, forced: false },
        // The actor is being taken from node 0. Node 2 is told to stand down.
        Event::Revoked { node: 2, new_epoch: 42 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!("the oracles accepted a revoke aimed at a bystander: {log:?}");
    };
    assert!(
        message.contains("claim 4"),
        "expected the transfer oracle to be the one that fired, got: {message}"
    );
}

/// A release from a node that was not handing the actor over is rejected.
///
/// `tr_complete_release` binds `from` from the current `Transferring`, so the
/// acknowledgement belongs to the outgoing owner. Nothing correlated the two:
/// a release credited to a bystander completed the transfer just as well.
#[test]
fn oracles_reject_a_release_from_a_node_outside_the_transfer() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 1, forced: false },
        // Node 2 is neither the outgoing owner nor the target.
        Event::Released { node: 2, new_epoch: 42 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!("the oracles accepted a release from a node outside the transfer: {log:?}");
    };
    assert!(
        message.contains("claim 4"),
        "expected the transfer oracle to be the one that fired, got: {message}"
    );
}

/// The same handover, released by the node that agreed to it, is fine.
///
/// The paired accept for both rejections above: it differs from the first in
/// the successor and from the second in the releasing node.
#[test]
fn oracles_accept_a_handover_released_by_its_outgoing_owner() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 1, forced: false },
        Event::Revoked { node: 0, new_epoch: 42 },
        Event::Released { node: 0, new_epoch: 42 },
        Event::Granted { node: 1, epoch: 42 },
        Event::Acquired { node: 1, epoch: 42 },
    ];

    assert!(
        check_invariants(&log).is_ok(),
        "a cooperative handover completed by the node that agreed to it is the \
         ordinary path and must be accepted: {log:?}"
    );
}

/// An offer naming an epoch the registry is not at is rejected.
///
/// `tr_issue_grant` publishes the registry's *current* epoch. A grant for any
/// other epoch is a capability the model never issues — a stale one, or one
/// for a future that has not happened.
///
/// The gap is the same half-implemented conjunct as `tr_acquire`, for the
/// third time: the grant oracle's comment said the epoch had to match and only
/// the node was checked, so a bare `Granted(0, 42)` at the start passed
/// everything. The epoch half now lives in the monotonicity loop, which reads
/// every event exposing where the registry is, rather than in a second tracker
/// beside it.
#[test]
fn oracles_reject_an_offer_naming_the_wrong_epoch() {
    let log = vec![Event::Granted { node: 0, epoch: 42 }];

    let Err(message) = check_invariants(&log) else {
        panic!(
            "the oracles accepted an offer for an epoch the registry has never \
             been at: {log:?}"
        );
    };
    assert!(
        message.contains("claim 5"),
        "expected the monotonicity oracle to be the one that fired, got: {message}"
    );
}

/// An aborted handover that goes to a third party is rejected.
///
/// `tr_abort_transfer` burns another epoch and offers the actor **back to the
/// node it was being taken from**. Clearing the pending transfer on any forced
/// burn, without checking where it went, meant an audited log could abort a
/// handover into somebody else's hands unremarked.
///
/// `an_interrupted_transfer_returns_to_the_node_it_came_from` pins the current
/// handler against this, and that is a different thing: a story checks the
/// implementation, an oracle checks any log. The implementation was right and
/// the oracle was not.
#[test]
fn oracles_reject_an_abort_that_goes_to_a_third_party() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 1, forced: false },
        // The handover from node 0 is aborted — and lands on node 2.
        Event::EpochBurned { from_epoch: 42, to_epoch: 43, next: 2, forced: true },
        Event::Granted { node: 2, epoch: 43 },
        Event::Acquired { node: 2, epoch: 43 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!("the oracles accepted an abort handing the actor to a third party: {log:?}");
    };
    assert!(
        message.contains("claim 4"),
        "expected the transfer oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the misdirected abort: {message}");
}

/// The same abort, going back where it came from, is fine.
///
/// The paired accept, differing in the successor alone.
#[test]
fn oracles_accept_an_abort_that_returns_the_actor() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 1, forced: false },
        Event::EpochBurned { from_epoch: 42, to_epoch: 43, next: 0, forced: true },
        Event::Granted { node: 0, epoch: 43 },
        Event::Acquired { node: 0, epoch: 43 },
    ];

    assert!(
        check_invariants(&log).is_ok(),
        "an aborted handover returning the actor to the node it was being taken \
         from is the model's only recovery from `Transferring` and must be \
         accepted: {log:?}"
    );
}

/// A write with no acquire behind it is rejected — P8, with a witness.
///
/// P8 checks that an acquire for this exact `(node, epoch)` came earlier. It
/// does not check that the acquire was still current, which sounds like a gap
/// until you notice the fencing oracle owns that case: a write at a superseded
/// epoch is below the burn high-water mark. So P8 is narrower than its name
/// suggests and is not wrong, and this is the log that shows it does its own
/// half.
///
/// Its paired accept is `oracles_accept_the_same_log_without_the_reassignment`,
/// which is this log with the acquire restored. That one test is the accept
/// side of two rejections, which is fine — what matters is that some accepted
/// log differs from the rejected one only in the thing being claimed.
#[test]
fn oracles_reject_a_write_with_no_capability() {
    let log = vec![Event::Wrote { node: 0, epoch: 41, seq: 1 }];

    let Err(message) = check_invariants(&log) else {
        panic!(
            "the oracles accepted a write from a node that never acquired \
             anything: {log:?}"
        );
    };
    assert!(
        message.contains("P8"),
        "expected the capability oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the uncapable write: {message}");
}

/// A registry that sits back down below an epoch it burned is rejected.
///
/// Hand-built for the same reason as the story below it: this coordinator
/// cannot produce it, because its epoch only ever increases, and an oracle
/// that is sound only because of that is not checking anything.
///
/// The gap was real and was the burns-only reading of claim 5. This log passed
/// the entire suite — the repeated owner satisfies the ownership check, and
/// with no writes in it, nothing else had anything to say — while the actor
/// returned to an epoch that had already been burned past.
#[test]
fn oracles_reject_a_registry_that_goes_backwards() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 0, forced: true },
        Event::Acquired { node: 0, epoch: 41 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!(
            "the oracles accepted a registry dropping back below an epoch it \
             had burned, so monotonicity is not being checked outside of burn \
             records: {log:?}"
        );
    };
    assert!(
        message.contains("claim 5"),
        "expected the monotonicity oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the regressing registry: {message}");
}

/// A registry that jumps forward with no burn recorded is rejected too.
///
/// The other half of the same failure, and the half a "never goes backwards"
/// reading cannot see. Nothing here regresses — 41 then 42 is monotone — but
/// the epoch moved without a burn, and in the model there is no such step:
/// every transition that changes the epoch burns it.
///
/// Found by turning the previous finding around rather than by being told, so
/// it gets a test for the same reason that one did.
#[test]
fn oracles_reject_an_epoch_that_moves_without_a_burn() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::Acquired { node: 1, epoch: 42 },
        Event::Wrote { node: 1, epoch: 42, seq: 1 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!(
            "the oracles accepted a registry moving from epoch 41 to 42 with no \
             burn recorded, so the epoch is not being accounted for: {log:?}"
        );
    };
    assert!(
        message.contains("claim 5"),
        "expected the monotonicity oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the unaccounted epoch: {message}");
}

/// The same shape going forwards is fine.
///
/// Paired with the test above so that it is rejecting the regression rather
/// than the shape — an oracle that refused every log containing two acquires
/// would pass that one just as well.
#[test]
fn oracles_accept_a_registry_that_moves_forward() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::EpochBurned { from_epoch: 41, to_epoch: 42, next: 0, forced: true },
        Event::Granted { node: 0, epoch: 42 },
        Event::Acquired { node: 0, epoch: 42 },
    ];

    assert!(
        check_invariants(&log).is_ok(),
        "a burn followed by an acquire at the new epoch is the ordinary \
         forced-revoke path and must be accepted: {log:?}"
    );
}

/// An epoch that changes hands without a burn is rejected.
///
/// The log here is hand-built rather than simulated, and that is the point.
/// This coordinator cannot produce it — `ACQUIRE` requires the registry to be
/// `Unowned` at exactly that epoch, so no ordering of real requests reaches it.
/// But the oracles exist to audit the coordinator, and an oracle that is sound
/// only because the thing it audits is correct is not auditing anything. It has
/// to reject a log the coordinator should never produce, on its own terms.
///
/// The gap was real: before this check existed, `check_invariants` read only
/// write epochs, which is a consequence of P5/P6 rather than the theorems
/// themselves. This exact log passed every oracle in the suite — one writer per
/// epoch for claim 1, no burn for claim 5 and for fencing, and node 1 really
/// had acquired, for P8 — while an epoch changed owner with nothing burned
/// between, which is precisely what "ownership at an epoch is final" and "an
/// epoch determines its owner" forbid.
#[test]
fn oracles_reject_an_epoch_that_changes_owner() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::Acquired { node: 1, epoch: 41 },
        Event::Wrote { node: 1, epoch: 41, seq: 1 },
    ];

    let Err(message) = check_invariants(&log) else {
        panic!(
            "the oracles accepted an epoch changing owner with no burn between, \
             so nothing in the suite is checking P5/P6 at all: {log:?}"
        );
    };
    assert!(
        message.contains("P5/P6"),
        "expected the ownership oracle to be the one that fired, got: {message}"
    );
    println!("oracles rejected the reassigned epoch: {message}");
}

/// And the same log with one acquire removed is fine, so the check above is
/// rejecting the reassignment rather than the shape.
///
/// Worth its own test because the previous one would pass just as well against
/// an oracle that rejected every log it was given.
#[test]
fn oracles_accept_the_same_log_without_the_reassignment() {
    let log = vec![
        Event::Granted { node: 0, epoch: 41 },
        Event::Acquired { node: 0, epoch: 41 },
        Event::Wrote { node: 0, epoch: 41, seq: 1 },
    ];

    assert!(
        check_invariants(&log).is_ok(),
        "a node acquiring an epoch it was offered and writing at it is the \
         ordinary case and must be accepted: {log:?}"
    );
}

/// Without it, the oracles catch it — and say the right thing about it.
///
/// This is the question every oracle has to answer about itself: would it
/// notice? A suite that cannot fail is indistinguishable from one that passes,
/// and a green run that only shows the assertions did not fire is very weak
/// evidence. So the *same* story runs again with one bit changed — the
/// coordinator stops checking writes against the registry — and the oracles
/// are required to reject the result.
///
/// It expects the *fencing* oracle, which it did not always. For a while
/// `check_invariants` carried a second P5/P6 half reading "accepted writes
/// never regress", that half ran first, and this test asserted on it — so the
/// suite reported a stale write as a violation of ownership finality. Nothing
/// about ownership was violated: the registry never changed hands at either
/// epoch, and what happened is that a write below the burned epoch was
/// accepted. The half was live only because it pre-empted the oracle that was
/// right, and this test was what held that in place.
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
        message.contains("claims 2/3"),
        "expected the fencing oracle to be the one that fired — a stale write \
         is a fencing failure, whatever else also notices it — got: {message}"
    );
    println!("oracles rejected the unfenced run: {message}");
}
