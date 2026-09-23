//! What a registry has to remember across a restart, and what goes wrong when
//! it does not.
//!
//! The model's registry — `System::actors` — is read and written in one step by
//! every epoch-advancing transition, and the README calls that the strongest
//! assumption it makes. It is really two assumptions under one name. The record
//! is updated **atomically**, and it **survives**. An `Arc<Mutex<..>>` supplies
//! the first and nothing at all of the second, and the half it leaves out is
//! the half every fencing theorem rests on: they assume epochs only ever go up,
//! and a registry that forgets can make them go down.
//!
//! These tests drive the `Registry` directly rather than over the wire. The
//! handover story is the one that has to go through Jetstream RPC, because what
//! it demonstrates is the service; what these demonstrate is what the service
//! remembers, and a simulated network between the caller and the fact under
//! test would only make the failure harder to read.
//!
//! Identity still arrives the way the service insists on: a `Context` carrying
//! the caller's address, never an argument naming a node.

use std::collections::HashMap;
use std::io;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;

use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;
use distributed_ownership::ownership::service::{
    EpochFloor, Event, FileFloor, MemoryFloor, Offer, Ownership, Registry,
};

const A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
const B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));

fn roster() -> HashMap<IpAddr, u64> {
    HashMap::from([(A, 0u64), (B, 1u64)])
}

/// A caller, identified the way the service identifies one: by where the
/// connection came from.
fn from(addr: IpAddr) -> Context {
    Context::new(Some(RemoteAddr::IpAddr(addr)), None)
}

fn registry(floor: &MemoryFloor) -> Registry {
    Registry::new(roster(), 0, Arc::new(floor.clone()))
        .expect("the floor is readable and node 0 is on the roster")
}

/// A owns the actor at 41 and hands it to B, which takes it at 42 and writes.
/// The registry is dropped at the end, which is the restart.
async fn a_hands_the_actor_to_b(reg: &Registry) {
    assert_eq!(reg.poll(from(A)).await.unwrap(), Offer::Grant(41));
    reg.acquire(from(A), 41).await.unwrap();
    assert_eq!(reg.write(from(A), 41).await.unwrap(), 1);

    reg.begin_transfer(from(A), 1).await.unwrap();
    assert_eq!(reg.poll(from(A)).await.unwrap(), Offer::Revoke(42));
    reg.release(from(A), 42).await.unwrap();

    assert_eq!(reg.poll(from(B)).await.unwrap(), Offer::Grant(42));
    reg.acquire(from(B), 42).await.unwrap();
    assert_eq!(reg.write(from(B), 42).await.unwrap(), 2);
}

/// The registry restarts and the actor does not go backwards.
///
/// A is partitioned away throughout, still believing it owns the actor at 41 —
/// which is a belief nothing can correct, because the whole point of a
/// partition is that A hears nothing. The registry is the only thing that can
/// keep that belief harmless, and it can only do so by never offering 41 again.
#[tokio::test]
async fn a_restarted_registry_does_not_reissue_an_epoch_it_already_used() {
    let floor = MemoryFloor::at(40);

    {
        let reg = registry(&floor);
        a_hands_the_actor_to_b(&reg).await;
    }

    // Everything the registry knew is gone: the state, the issued grants, the
    // log. All that survives is the floor.
    let reg = registry(&floor);

    assert_eq!(
        reg.poll(from(A)).await.unwrap(),
        Offer::Grant(43),
        "the new registry must start above every epoch the old one used, not at \
         a number somebody passed it"
    );

    // And A, which never learned any of this, is refused.
    let fenced = reg
        .write(from(A), 41)
        .await
        .expect_err("a write at an epoch from before the restart must be refused");
    assert_eq!(fenced.code(), Some("FENCED"), "{fenced:?}");
    assert!(
        reg.log().contains(&Event::Fenced { node: 0, epoch: 41 }),
        "and the refusal has to be in the new registry's log, or no auditor \
         could ever see that it happened: {:?}",
        reg.log()
    );
}

/// The same run against a registry that forgot, so the defect is on the record
/// rather than only its absence.
///
/// This is the check in the other direction. The test above passes for two
/// quite different reasons — because the floor works, or because the assertions
/// are too weak to notice it failing — and only a run with the floor taken away
/// tells them apart. Every assertion here states something the protocol
/// forbids, and the test passes because the unguarded code really does it.
#[tokio::test]
async fn a_forgetful_registry_unfences_the_owner_it_had_already_fenced() {
    {
        let floor = MemoryFloor::at(40);
        let reg = registry(&floor);
        a_hands_the_actor_to_b(&reg).await;
    }

    // A fresh floor, seeded exactly as the first one was: a registry that wrote
    // nothing down and comes back where it started.
    let amnesiac = MemoryFloor::at(40);
    let reg = registry(&amnesiac);

    assert_eq!(
        reg.poll(from(A)).await.unwrap(),
        Offer::Grant(41),
        "an epoch that was burned before the restart is on offer again"
    );
    reg.acquire(from(A), 41).await.unwrap();
    assert_eq!(
        reg.write(from(A), 41).await.unwrap(),
        1,
        "and the node the protocol had already fenced out is writing again, at \
         the very epoch it was fenced at"
    );

    // Which is not merely untidy. B really did own the actor at 42, and is now
    // the one refused: the actor has moved backwards, and the node holding the
    // later epoch is the one that looks stale.
    let fenced = reg.write(from(B), 42).await.unwrap_err();
    assert_eq!(
        fenced.code(),
        Some("FENCED"),
        "the holder of the *later* epoch is the one being fenced: {fenced:?}"
    );
}

/// A floor that cannot be written leaves the registry exactly where it was.
///
/// The ordering is the whole claim: the new epoch is recorded *before* the
/// state that depends on it becomes visible, so a failure to record is a
/// request that did not happen rather than a handover half-done. Failing the
/// other way round — burn the epoch, then fail to write it down — is the
/// forgetful registry above, reached without a restart.
#[tokio::test]
async fn a_failed_record_leaves_the_actor_untouched() {
    /// Readable, and writable exactly once: enough for `Registry::new` to
    /// record its starting epoch, and not enough for the first burn.
    struct FailsAfterTheFirstEpoch;

    impl EpochFloor for FailsAfterTheFirstEpoch {
        fn read(&self) -> io::Result<u64> {
            Ok(40)
        }

        fn record(&self, epoch: u64) -> io::Result<()> {
            if epoch <= 41 {
                Ok(())
            } else {
                Err(io::Error::other("the floor is gone"))
            }
        }
    }

    let reg = Registry::new(roster(), 0, Arc::new(FailsAfterTheFirstEpoch)).unwrap();
    assert_eq!(reg.poll(from(A)).await.unwrap(), Offer::Grant(41));
    reg.acquire(from(A), 41).await.unwrap();
    assert_eq!(reg.write(from(A), 41).await.unwrap(), 1);

    let down = reg
        .begin_transfer(from(A), 1)
        .await
        .expect_err("a handover whose epoch cannot be made durable must not proceed");
    assert_eq!(
        down.code(),
        Some("DOWN"),
        "and it is not a protocol refusal: nothing about the actor's state made \
         this request illegal, so `NO` would tell an auditor something false — \
         {down:?}"
    );

    // A still owns the actor at 41, because nothing happened.
    assert_eq!(
        reg.write(from(A), 41).await.unwrap(),
        2,
        "the owner must be unaffected by a handover that did not happen"
    );
    assert!(
        !reg.log()
            .iter()
            .any(|e| matches!(e, Event::EpochBurned { .. })),
        "and no burn may be recorded for an epoch that was never made durable: {:?}",
        reg.log()
    );

    // B is not the owner either, so the actor is not in some third place.
    assert_eq!(reg.poll(from(B)).await.unwrap(), Offer::Nothing);
}

/// `force` says which node the actor ended up offered to, which is not always
/// the one it was asked for.
///
/// From `Owned` and `Unowned` the coordinator's choice stands. From
/// `Transferring` the model gives it no way to redirect an interrupted
/// handover — `tr_abort_transfer` offers the actor back to the node it was
/// being taken from — so the answer differs from the request, and saying so is
/// the difference between a caller knowing where the actor is and assuming.
#[tokio::test]
async fn force_reports_where_the_actor_actually_went() {
    let floor = MemoryFloor::at(40);
    let reg = registry(&floor);

    // From `Owned`: A holds the actor, the coordinator hands it to B.
    assert_eq!(reg.poll(from(A)).await.unwrap(), Offer::Grant(41));
    reg.acquire(from(A), 41).await.unwrap();
    assert_eq!(reg.force(1).unwrap(), 1, "tr_revoke_owner names its successor");

    // From `Transferring`: B has the actor and has agreed to hand it back to A.
    assert_eq!(reg.poll(from(B)).await.unwrap(), Offer::Grant(42));
    reg.acquire(from(B), 42).await.unwrap();
    reg.begin_transfer(from(B), 0).await.unwrap();
    assert_eq!(
        reg.force(0).unwrap(),
        1,
        "the coordinator asked for node 0 and the answer is node 1: an \
         interrupted transfer goes back to the node it came from, and saying \
         `Ok(())` here would have let the caller believe otherwise"
    );

    // And the actor really is there, so the returned number is a fact about the
    // registry rather than a politeness.
    assert_eq!(reg.poll(from(A)).await.unwrap(), Offer::Nothing);
    assert_eq!(reg.poll(from(B)).await.unwrap(), Offer::Grant(44));
}

/// A node that is not on the roster cannot be handed the actor, including at
/// construction.
///
/// `is_node` stops it in `force` and `begin_transfer`. `Registry::new` was the
/// one place still setting `intended` without asking, and an actor held for a
/// node that cannot connect is held for nobody: `poll` only ever offers to
/// `intended`, so nothing later repairs it.
#[test]
fn a_registry_cannot_be_started_holding_the_actor_for_a_stranger() {
    let floor = MemoryFloor::at(40);
    assert!(Registry::new(roster(), 7, Arc::new(floor)).is_err());
}

/// A grant the registry published by *moving* the actor is a grant it has
/// issued.
///
/// Four of the model's transitions put a `Grant` on the network, not one:
/// `tr_issue_grant` and the four that offer the actor on as part of moving it.
/// The registry recorded only the first, so its idea of which grants existed
/// disagreed with the model's — and `granted` is an *input* to the verified
/// acquire step, so the disagreement was not a missing convenience. It meant
/// the refusal theorem was being applied under a hypothesis that did not hold.
#[tokio::test]
async fn a_release_publishes_the_grant_the_model_says_it_publishes() {
    let floor = MemoryFloor::at(40);
    let reg = registry(&floor);

    // The initial state has no published grant, and that is the model rather
    // than an omission: `init` gives every actor an `Unowned` record and an
    // **empty** network, which is the whole reason `tr_issue_grant` exists. So
    // the first offer still has to be asked for.
    let refused = reg
        .acquire(from(A), 41)
        .await
        .expect_err("the actor is held for A at 41, but nothing has been offered yet");
    assert_eq!(refused.code(), Some("NO"), "{refused:?}");

    assert_eq!(reg.poll(from(A)).await.unwrap(), Offer::Grant(41));
    reg.acquire(from(A), 41).await.unwrap();
    reg.begin_transfer(from(A), 1).await.unwrap();
    reg.release(from(A), 42).await.unwrap();

    // `tr_complete_release` publishes `Grant { to, new_epoch }` in the same
    // step, so B does not have to ask. Refusing here was the registry's own
    // bookkeeping contradicting the transition it had just taken.
    reg.acquire(from(B), 42)
        .await
        .expect("the release published B's grant, so B may take the actor");
    assert_eq!(reg.write(from(B), 42).await.unwrap(), 1);

    // And an auditor can see it, because a grant recorded but not logged makes
    // a perfectly legal `Acquired` look like an acquire of something that was
    // never offered — `Standing` and the P8 tracker both rebuild "which grants
    // were issued" from `Granted` alone.
    assert!(
        reg.log().contains(&Event::Granted { node: 1, epoch: 42 }),
        "the published grant has to be in the log, not only in the registry's \
         head: {:?}",
        reg.log()
    );
}

/// The same for a forced revoke, whose three transitions all publish one.
#[tokio::test]
async fn a_forced_revoke_publishes_the_grant_too() {
    let floor = MemoryFloor::at(40);
    let reg = registry(&floor);
    assert_eq!(reg.poll(from(A)).await.unwrap(), Offer::Grant(41));
    reg.acquire(from(A), 41).await.unwrap();

    assert_eq!(reg.force(1).unwrap(), 1);
    reg.acquire(from(B), 42)
        .await
        .expect("tr_revoke_owner publishes the successor's grant as it moves the actor");
}

/// An interrupted transfer is recoverable even when the coordinator names a
/// node that does not exist.
///
/// `tr_abort_transfer` does not mention `next` at all — the actor goes back to
/// the node the transfer came from — so validating it was a check on an
/// argument the transition never reads, and it refused the one step that
/// unsticks a half-finished handover. A liveness bug produced entirely by an
/// unnecessary validity check.
#[tokio::test]
async fn an_abort_does_not_need_a_successor_it_will_not_use() {
    let floor = MemoryFloor::at(40);
    let reg = registry(&floor);
    assert_eq!(reg.poll(from(A)).await.unwrap(), Offer::Grant(41));
    reg.acquire(from(A), 41).await.unwrap();
    reg.begin_transfer(from(A), 1).await.unwrap();

    // Node 9 is not on the roster.
    assert_eq!(
        reg.force(9).unwrap(),
        0,
        "an interrupted transfer goes back to node 0, and the successor the \
         coordinator named is never consulted"
    );
    assert_eq!(reg.poll(from(A)).await.unwrap(), Offer::Grant(43));

    // And from a state where the successor *is* consulted, a stranger is still
    // refused — so the change is about which transition is being taken rather
    // than about giving up on the roster.
    reg.acquire(from(A), 43).await.unwrap();
    let refused = reg.force(9).unwrap_err();
    assert_eq!(refused.code(), Some("ERR"), "{refused:?}");
}

/// The file-backed floor: monotone, and absent means zero rather than an error.
#[test]
fn the_file_floor_is_a_high_water_mark() {
    let path = std::env::temp_dir().join(format!(
        "jetstream-ownership-floor-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let _ = std::fs::remove_file(&path);
    let floor = FileFloor::new(&path);

    assert_eq!(floor.read().unwrap(), 0, "a floor that was never written is 0");

    floor.record(41).unwrap();
    assert_eq!(floor.read().unwrap(), 41);
    assert_eq!(
        FileFloor::new(&path).read().unwrap(),
        41,
        "and a different handle on the same path reads it, which is the only \
         thing that makes it durable rather than remembered"
    );

    floor.record(7).unwrap();
    assert_eq!(
        floor.read().unwrap(),
        41,
        "recording an earlier epoch is a no-op, not a move backwards"
    );

    floor.record(42).unwrap();
    assert_eq!(floor.read().unwrap(), 42);

    let _ = std::fs::remove_file(&path);
}

/// A floor named by a bare filename still works.
///
/// `Path::parent` of `"floor"` is the empty path — it names the current
/// directory but cannot be opened — and the first version of `record` took that
/// as licence to skip the directory `fsync`, which is what makes the rename
/// durable. Syncing `.` instead is the fix, and this is its regression guard.
///
/// Be clear about what it does and does not show: it cannot demonstrate
/// durability, because that needs a power cut. What it demonstrates is that the
/// path which previously *skipped* the sync now *takes* it without failing —
/// the way the fix could have been wrong.
#[test]
fn a_floor_named_by_a_bare_filename_still_records() {
    let name = format!("jetstream-bare-floor-{}", std::process::id());
    let _ = std::fs::remove_file(&name);

    let floor = FileFloor::new(&name);
    assert_eq!(floor.read().unwrap(), 0);
    floor.record(41).unwrap();
    assert_eq!(floor.read().unwrap(), 41);
    assert_eq!(FileFloor::new(&name).read().unwrap(), 41);

    let _ = std::fs::remove_file(&name);
}
