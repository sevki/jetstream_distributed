//! Algorithm 4, line by line.
//!
//! `proposer::absorb` is the paper's proposer loop with the I/O taken out: the state a
//! proposer holds, the replies a quorum gave, and what that does. These tests are the
//! paper's rules, one each, so a change that departs from the paper fails *here*, named,
//! before it shows up as a disagreement in `tests/consensus_contract.rs`.
//!
//! Tested, not verified: nothing proves this is the broadcast the abstract algorithm
//! assumes.

use jetstream_distributed::quepaxa::proposal::{LEADER, Proposal, pack, unpack};
use jetstream_distributed::quepaxa::service::Reply;
use jetstream_distributed::quepaxa::service::proposer::{Outcome, State, absorb, outgoing};
use rand::SeedableRng as _;

fn prop(priority: u32, proposer: u32, value: u64) -> u128 {
    pack(Proposal {
        priority,
        proposer,
        value,
    })
}

/// A recorder that is at `step`, first saw `first` there, and aggregated `prior` before.
fn reply(step: u64, first: u128, prior: u128) -> Reply {
    Reply { step, first, prior }
}

fn at(step: u64, proposal: u128) -> State {
    State {
        step,
        proposal,
        index: 1,
        leader: false,
    }
}

#[test]
fn a_proposer_starts_at_step_four_with_the_leaders_priority_template() {
    let s = State::start(2, false, 77);
    assert_eq!(s.step, 4, "round 1, phase 0");
    let p = unpack(s.proposal);
    assert_eq!((p.priority, p.proposer, p.value), (LEADER, 2, 77));
}

/// Phase 0, the fast path: every first value is the leader's, so a quorum already holds
/// the leader's proposal and its value is decided at once.
#[test]
fn phase_0_decides_when_every_first_value_is_the_leaders() {
    let mut s = at(4, prop(5, 1, 9));
    let leader = prop(LEADER, 0, 42);
    let out = absorb(&mut s, &[reply(4, leader, 0), reply(4, leader, 0)]);
    assert_eq!(out, Outcome::Decided(42));
}

/// ...and not when even one first value is another proposer's.
#[test]
fn phase_0_does_not_decide_when_one_first_value_is_not_the_leaders() {
    let mut s = at(4, prop(5, 1, 9));
    let leader = prop(LEADER, 0, 42);
    let other = prop(77, 2, 8);
    let out = absorb(&mut s, &[reply(4, leader, 0), reply(4, other, 0)]);
    assert_eq!(out, Outcome::Continue);
    // The best first value, which is the leader's, becomes the proposal; on to phase 1.
    assert_eq!(s.proposal, leader);
    assert_eq!(s.step, 5);
}

/// Phase 0 otherwise adopts the best of the first values, by priority and then proposer.
#[test]
fn phase_0_adopts_the_best_first_value() {
    let mut s = at(8, prop(1, 1, 1));
    let low = prop(10, 3, 100);
    let high = prop(11, 0, 200);
    assert_eq!(
        absorb(&mut s, &[reply(8, low, 0), reply(8, high, 0)]),
        Outcome::Continue
    );
    assert_eq!(s.proposal, high);
    assert_eq!(s.step, 9);
}

/// Phase 1 only spreads: nothing to decide or adopt.
#[test]
fn phase_1_spreads_and_changes_nothing_but_the_step() {
    let mut s = at(5, prop(9, 1, 3));
    let before = s.proposal;
    assert_eq!(
        absorb(&mut s, &[reply(5, prop(1, 2, 2), 0), reply(5, before, 0)]),
        Outcome::Continue
    );
    assert_eq!(s.proposal, before);
    assert_eq!(s.step, 6);
}

/// Phase 2: decide if my proposal is the best of the aggregates of phase 1.
#[test]
fn phase_2_decides_when_my_proposal_is_the_best_aggregate() {
    let mine = prop(9, 1, 3);
    let mut s = at(6, mine);
    let out = absorb(&mut s, &[reply(6, 0, mine), reply(6, 0, prop(4, 2, 4))]);
    assert_eq!(out, Outcome::Decided(3));
}

#[test]
fn phase_2_does_not_decide_when_a_better_proposal_was_spread() {
    let mine = prop(9, 1, 3);
    let better = prop(10, 2, 4);
    let mut s = at(6, mine);
    assert_eq!(
        absorb(&mut s, &[reply(6, 0, mine), reply(6, 0, better)]),
        Outcome::Continue
    );
    assert_eq!(
        s.step, 7,
        "phase 2 does not change the proposal; phase 3 does"
    );
    assert_eq!(s.proposal, mine);
}

/// Phase 3: the proposal for next round is the best of the phase-2 aggregates.
#[test]
fn phase_3_adopts_the_best_aggregate_for_the_next_round() {
    let mut s = at(7, prop(1, 1, 1));
    let best = prop(30, 2, 5);
    assert_eq!(
        absorb(&mut s, &[reply(7, 0, prop(20, 0, 6)), reply(7, 0, best)]),
        Outcome::Continue
    );
    assert_eq!(s.proposal, best);
    assert_eq!(s.step, 8, "the next round's phase 0");
}

/// Catching up: a recorder ahead makes the proposer jump to its step and adopt the first
/// value it recorded there, whatever phase it was in.
#[test]
fn a_proposer_catches_up_to_the_furthest_recorder() {
    let mut s = at(5, prop(1, 1, 1));
    let theirs = prop(50, 2, 9);
    let out = absorb(&mut s, &[reply(5, prop(1, 1, 1), 0), reply(11, theirs, 0)]);
    assert_eq!(out, Outcome::Continue);
    assert_eq!(s.step, 11);
    assert_eq!(s.proposal, theirs);
}

#[test]
fn catching_up_takes_the_furthest_when_several_are_ahead() {
    let mut s = at(4, prop(1, 1, 1));
    let near = prop(2, 0, 2);
    let far = prop(3, 0, 3);
    absorb(&mut s, &[reply(6, near, 0), reply(9, far, 0)]);
    assert_eq!((s.step, s.proposal), (9, far));
}

/// What is sent: at phase 0 each recorder gets its own random priority in `1..LEADER`,
/// except the designated leader's first round.
#[test]
fn phase_0_sends_each_recorder_its_own_random_priority() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(1);
    let s = at(8, prop(LEADER, 1, 5));
    let sent = outgoing(&s, 5, &mut rng);
    assert_eq!(sent.len(), 5);
    let priorities: Vec<u32> = sent.iter().map(|&p| unpack(p).priority).collect();
    assert!(
        priorities.iter().all(|&p| (1..LEADER).contains(&p)),
        "{priorities:?}"
    );
    assert!(
        priorities.windows(2).any(|w| w[0] != w[1]),
        "independent per recorder"
    );
    // Same proposer, same value: only the priority differs.
    assert!(
        sent.iter()
            .all(|&p| (unpack(p).proposer, unpack(p).value) == (1, 5))
    );
}

#[test]
fn the_leader_keeps_the_top_priority_in_its_first_round_only() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(2);
    let first = State {
        step: 4,
        proposal: prop(LEADER, 0, 5),
        index: 0,
        leader: true,
    };
    assert!(
        outgoing(&first, 3, &mut rng)
            .iter()
            .all(|&p| unpack(p).priority == LEADER)
    );
    let later = State { step: 8, ..first };
    assert!(
        outgoing(&later, 3, &mut rng)
            .iter()
            .all(|&p| unpack(p).priority < LEADER)
    );
    // A non-leader's first round is randomised too.
    let other = State {
        step: 4,
        proposal: prop(LEADER, 1, 5),
        index: 1,
        leader: false,
    };
    assert!(
        outgoing(&other, 3, &mut rng)
            .iter()
            .all(|&p| unpack(p).priority < LEADER)
    );
}

/// At every other phase the proposal is sent as it is.
#[test]
fn other_phases_send_the_proposal_unchanged() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(3);
    let p = prop(1234, 1, 5);
    for step in [5, 6, 7, 9, 10, 11] {
        assert_eq!(
            outgoing(&at(step, p), 3, &mut rng),
            vec![p, p, p],
            "step {step}"
        );
    }
}
