//! **One contract, every consensus protocol.**
//!
//! `jetstream_distributed::consensus::ReplicatedLog` is the interface a consumer
//! depends on, and [`obeys_the_contract`] is the test written against it. It knows
//! nothing about any protocol: it proposes unique values at several replicas at once,
//! retrying elsewhere when a replica declines, and then checks the six properties in
//! the trait's docs. Each implementation builds a cluster and runs it through here.
//!
//! The checks are *tests*, on in-process runs with injected loss, delay and crashed
//! replicas. What each protocol proves of its own model is in its own Reference page.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::net::{IpAddr, Ipv4Addr};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;
use jetstream_distributed::consensus::{Decision, ProposeError, ReplicatedLog};
use jetstream_distributed::quepaxa::service::proposer::Config;
use jetstream_distributed::quepaxa::service::{
    Proposer, QuePaxaLog, Recorder, RecorderNode, Reply,
};
use rand::RngExt as _;
use rand::SeedableRng as _;

// ---------------------------------------------------------------------------
// The contract
// ---------------------------------------------------------------------------

/// Propose `value` at `prefer` first and then at the others in turn, until some replica
/// decides it. Returns who did, and what it said.
async fn propose_somewhere<L: ReplicatedLog>(
    replicas: &[Arc<L>],
    prefer: usize,
    value: u64,
) -> (usize, Decision) {
    for attempt in 0..400 {
        let who = (prefer + attempt) % replicas.len();
        match replicas[who].propose(value).await {
            Ok(decision) => return (who, decision),
            // Not this one's to propose: try the next.
            Err(ProposeError::NotPlaced(_)) => {}
            // Could not tell. The value may even have been decided; asking again is
            // allowed to put it in the log twice, which the checks below allow.
            Err(ProposeError::Unavailable(_)) => tokio::task::yield_now().await,
        }
    }
    panic!("no replica could decide {value}");
}

/// Run `per_replica` unique proposals from each of `proposers` replicas at once, then
/// check the contract.
///
/// `proposers` is how many of the first replicas propose; the rest only learn, which is
/// how a crashed or passive replica is represented.
async fn obeys_the_contract<L: ReplicatedLog + 'static>(
    replicas: Vec<Arc<L>>,
    proposers: usize,
    per_replica: u64,
) {
    let mut tasks = Vec::new();
    for i in 0..proposers {
        let replicas = replicas.clone();
        tasks.push(tokio::spawn(async move {
            let mut got = Vec::new();
            for k in 0..per_replica {
                // Unique, and never 0.
                let value = ((i as u64 + 1) << 32) | (k + 1);
                got.push((value, propose_somewhere(&replicas, i, value).await));
            }
            got
        }));
    }
    let mut proposed = BTreeSet::new();
    let mut returned: Vec<(u64, usize, Decision)> = Vec::new();
    for task in tasks {
        for (value, (who, decision)) in task.await.expect("a proposer panicked") {
            proposed.insert(value);
            returned.push((value, who, decision));
        }
    }

    // 4. No two proposals share a slot: a slot holds one value.
    let mut at: BTreeMap<u64, u64> = BTreeMap::new();
    for &(value, _, d) in &returned {
        assert_eq!(d.value, value, "a successful propose(v) decides v");
        if let Some(&other) = at.get(&d.slot) {
            assert_eq!(
                other, value,
                "slot {} was returned for two different values",
                d.slot
            );
        }
        at.insert(d.slot, value);
    }

    // 3. A decision is visible to the replica that returned it.
    for &(value, who, d) in &returned {
        assert_eq!(
            replicas[who].decided(d.slot).await,
            Some(value),
            "replica {who} returned slot {} for {value} and does not know it",
            d.slot
        );
    }

    // 1. Agreement and 2. validity, over every slot anyone might have decided.
    let horizon = at.keys().max().map_or(0, |m| m + 8);
    let mut snapshot: BTreeMap<(usize, u64), u64> = BTreeMap::new();
    for slot in 0..horizon {
        let mut seen: BTreeSet<u64> = BTreeSet::new();
        for (r, replica) in replicas.iter().enumerate() {
            if let Some(v) = replica.decided(slot).await {
                assert!(
                    proposed.contains(&v),
                    "slot {slot} decided {v}, which nobody proposed"
                );
                seen.insert(v);
                snapshot.insert((r, slot), v);
            }
        }
        assert!(
            seen.len() <= 1,
            "slot {slot} was decided differently at different replicas: {seen:?}"
        );
    }

    // 5. `committed` is a prefix.
    for (r, replica) in replicas.iter().enumerate() {
        let n = replica.committed().await;
        for slot in 0..n {
            assert!(
                replica.decided(slot).await.is_some(),
                "replica {r}: committed {n} but slot {slot} is not decided"
            );
        }
    }

    // 6. A decision never changes.
    for _ in 0..8 {
        tokio::task::yield_now().await;
    }
    for (&(r, slot), &v) in &snapshot {
        assert_eq!(
            replicas[r].decided(slot).await,
            Some(v),
            "replica {r} changed slot {slot}"
        );
    }

    // Every proposal got a slot: nothing was lost.
    let in_log: BTreeSet<u64> = at.values().copied().collect();
    assert_eq!(
        in_log, proposed,
        "every proposed value is in the log, and nothing else"
    );
}

// ---------------------------------------------------------------------------
// QuePaxa
// ---------------------------------------------------------------------------

/// What can go wrong on a link, from the proposer's side.
struct Faults {
    /// Chance in a thousand that a call is lost (answered with an error).
    loss: u32,
    /// A crashed recorder never answers.
    crashed: AtomicBool,
    rng: Mutex<rand::rngs::StdRng>,
}

impl Faults {
    fn new(seed: u64, loss: u32) -> Arc<Faults> {
        Arc::new(Faults {
            loss,
            crashed: AtomicBool::new(false),
            rng: Mutex::new(rand::rngs::StdRng::seed_from_u64(seed)),
        })
    }

    /// Let other tasks run for a random while, and then drop the call or let it through.
    async fn gate(&self) -> Result<()> {
        if self.crashed.load(Ordering::SeqCst) {
            std::future::pending::<()>().await;
        }
        let (lost, yields) = {
            let mut rng = self.rng.lock().unwrap();
            (
                rng.random_range(0..1000) < self.loss,
                rng.random_range(0..4),
            )
        };
        for _ in 0..yields {
            tokio::task::yield_now().await;
        }
        if lost {
            return Err(Error::new("lost").set_code("LOST"));
        }
        Ok(())
    }
}

/// A recorder in this process, reached through a link that can fail, as the member at
/// `from`.
struct Link {
    node: RecorderNode,
    from: IpAddr,
    faults: Arc<Faults>,
}

impl Link {
    fn ctx(&self) -> Context {
        Context::new(Some(RemoteAddr::IpAddr(self.from)), None)
    }
}

impl Recorder for Link {
    async fn record(&self, _ctx: Context, slot: u64, step: u64, value: u128) -> Result<Reply> {
        self.faults.gate().await?;
        self.node.record(self.ctx(), slot, step, value).await
    }

    async fn learn(&self, _ctx: Context, slot: u64, value: u64) -> Result<()> {
        self.faults.gate().await?;
        self.node.learn(self.ctx(), slot, value).await
    }
}

fn member(i: usize) -> IpAddr {
    IpAddr::V4(Ipv4Addr::new(10, 0, 0, i as u8 + 1))
}

/// `n` replicas, each a recorder and a proposer over all of them. `crashed` replicas'
/// recorders never answer anyone. Every link has `loss` chance in a thousand of losing
/// a call.
fn quepaxa_cluster(
    n: usize,
    crashed: &[usize],
    loss: u32,
    seed: u64,
) -> Vec<Arc<QuePaxaLog<Link>>> {
    let roster: HashMap<IpAddr, u32> = (0..n).map(|i| (member(i), i as u32)).collect();
    let nodes: Vec<RecorderNode> = (0..n).map(|_| RecorderNode::new(roster.clone())).collect();
    (0..n)
        .map(|i| {
            let links = (0..n)
                .map(|j| {
                    let faults = Faults::new(
                        seed * 1000 + (i * n + j) as u64,
                        if i == j { 0 } else { loss },
                    );
                    if crashed.contains(&j) {
                        faults.crashed.store(true, Ordering::SeqCst);
                    }
                    Link {
                        node: nodes[j].clone(),
                        from: member(i),
                        faults,
                    }
                })
                .collect();
            let config = Config {
                index: i as u32,
                // Replica 0 is the designated leader; the others hedge behind it.
                leader: i == 0,
                hedge: std::time::Duration::ZERO,
                seed: Some(seed * 77 + i as u64),
            };
            Arc::new(QuePaxaLog::new(
                nodes[i].clone(),
                Proposer::new(config, links),
            ))
        })
        .collect()
}

#[tokio::test]
async fn quepaxa_obeys_the_contract_when_nothing_fails() {
    for seed in 0..10 {
        obeys_the_contract(quepaxa_cluster(3, &[], 0, seed), 3, 4).await;
    }
}

#[tokio::test]
async fn quepaxa_obeys_the_contract_with_one_proposer() {
    obeys_the_contract(quepaxa_cluster(3, &[], 0, 1), 1, 6).await;
}

/// **A proposer proposes one value per slot.**
///
/// Found by this suite: the harness retried a value at the designated leader's replica
/// while that replica was already proposing another at the same slot, so two proposals
/// with the same proposer id and the leader's priority were in one slot, and two
/// replicas decided it differently. A proposer must not do that, and `Proposer` now
/// refuses to: a second value for a slot it has run is replaced by the first.
#[tokio::test]
async fn a_proposer_puts_one_value_in_a_slot() {
    let cluster = quepaxa_cluster(3, &[], 0, 5);
    // Two different values at the same replica, at the same time. Whichever the
    // replica's proposer ran first at the slot is what both carry.
    let (a, b) = tokio::join!(cluster[0].propose(0x11), cluster[0].propose(0x22));
    let (a, b) = (a.unwrap(), b.unwrap());
    assert_ne!(a.slot, b.slot, "they cannot share a slot");
    for d in [a, b] {
        assert_eq!(cluster[0].decided(d.slot).await, Some(d.value));
        for replica in &cluster {
            if let Some(v) = replica.decided(d.slot).await {
                assert_eq!(v, d.value, "every replica that knows agrees");
            }
        }
    }
}

#[tokio::test]
async fn quepaxa_obeys_the_contract_when_calls_are_lost() {
    for seed in 0..25 {
        obeys_the_contract(quepaxa_cluster(3, &[], 150, seed), 3, 3).await;
    }
}

#[tokio::test]
async fn quepaxa_obeys_the_contract_with_a_crashed_minority() {
    // Replica 2 of 3 never answers: the other two are a majority and carry on.
    for seed in 0..10 {
        obeys_the_contract(quepaxa_cluster(3, &[2], 0, seed), 2, 4).await;
    }
    // Two of five.
    for seed in 0..10 {
        obeys_the_contract(quepaxa_cluster(5, &[3, 4], 100, seed), 3, 3).await;
    }
}

#[tokio::test]
async fn quepaxa_obeys_the_contract_with_five_replicas_all_proposing() {
    for seed in 0..10 {
        obeys_the_contract(quepaxa_cluster(5, &[], 100, seed), 5, 3).await;
    }
}
