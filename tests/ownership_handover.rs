//! The headline story, against the real service.
//!
//! A owns the actor at epoch 41 and writes. A agrees to hand it to B, which
//! burns the epoch. A — not yet knowing, or not caring — writes again at 41 and
//! is **fenced**. B takes the actor at 42 and writes.
//!
//! That one refusal is the whole point of the protocol, and until now it had
//! only ever been demonstrated against a hand-written stand-in speaking a line
//! protocol over a socket. Here it is demonstrated against a Jetstream service,
//! over Jetstream's own RPC, with the fence performed by `FenceGuard::accepts`
//! — the one function in this repository proved to agree with the model's
//! `may_mutate`.
//!
//! Sequencing is on the audit log, not on the clock. B waits until the log
//! shows A's `Released` before taking the actor, so "B starts after A has
//! finished" is a condition the run establishes rather than a duration it
//! hopes is long enough.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use jetstream::prelude::*;
// The `#[service]` macro puts the generated client and server in a
// `<trait>_protocol` module and leaves the trait itself at the crate root —
// `pub mod ownership_protocol { pub struct OwnershipService<T: Ownership> { pub
// inner: T }, pub struct OwnershipChannel }`. The trait has to be in scope
// because the channel reaches the registry through `impl Ownership for
// OwnershipChannel`, not through inherent methods.
use jetstream_distributed::ownership::service::{
    ownership_protocol::{OwnershipChannel, OwnershipService},
    Event, MemoryFloor, Offer, Ownership, Registry,
};
use jetstream_rpc::session::{Session, SingleLaneSession};
use turmoil::net::{TcpListener, TcpStream};

const PORT: u16 = 9000;

// Connecting is written out in each client rather than factored into a helper,
// and that is deliberate: the `Session` owns the lane's I/O, so a helper that
// builds one and returns only the channel drops it on the way out and the next
// call fails with "session is closed". It has to outlive every request made on
// the channel, which means living in the caller's scope.
macro_rules! connect {
    ($session:ident, $channel:ident) => {
        let stream = TcpStream::connect(("registry", PORT))
            .await
            .expect("the registry is listening");
        let $session = SingleLaneSession::<OwnershipChannel, _, _>::client_io(stream);
        let lane = Session::<OwnershipChannel>::open_lane(&$session)
            .await
            .expect("the one lane is available");
        let $channel = OwnershipChannel::new(64, Box::new(lane));
        // "Must be called after `new()` and before any RPC calls", per the
        // generated client. Every non-test client in jetstream does this.
        $channel
            .negotiate_version(u32::MAX)
            .await
            .expect("the server speaks this protocol version");
    };
}

#[test]
fn a_handover_fences_the_outgoing_owner() {
    let mut sim = turmoil::Builder::new().build();

    // The registry is built *inside* the host, because `turmoil::lookup` needs a
    // live simulation to resolve a name and panics without one — every other
    // use of it in this repository is inside a host for the same reason. It is
    // shared back out so the audit log can be read once the run is over.
    let shared: Arc<OnceLock<Registry>> = Arc::new(OnceLock::new());

    // Seeded at 40 so the registry's first epoch is 41 and the story below is
    // the one the model's scenario tells. The number is the *floor's*, not the
    // registry's: `Registry::new` reads it rather than being handed a starting
    // epoch, which is what stops a restart rewinding the actor. See
    // `tests/durability.rs`.
    let floor = MemoryFloor::at(40);

    let built = shared.clone();
    let seeded = floor.clone();
    sim.host("registry", move || {
        let built = built.clone();
        let seeded = seeded.clone();
        async move {
            // Who is which node, by address. See the crate docs: an address is
            // not a credential, but in a simulated network nothing can spoof
            // one, and the shape — identity arriving with the connection
            // rather than in an argument — is what carries over to TLS.
            let served = built
                .get_or_init(|| {
                    let roster = HashMap::from([
                        (turmoil::lookup("a"), 0),
                        (turmoil::lookup("b"), 1),
                    ]);
                    Registry::new(roster, 0, Arc::new(seeded.clone()))
                        .expect("the floor is readable and node 0 is on the roster")
                })
                .clone();
            let listener =
                TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
            loop {
                let (stream, _) = listener.accept().await?;
                let served = served.clone();
                tokio::spawn(async move {
                    let session =
                        SingleLaneSession::<OwnershipChannel, _, _>::service_io(stream);
                    let Ok(lane) = Session::<OwnershipChannel>::accept_lane(&session).await
                    else {
                        return;
                    };
                    let mut service = OwnershipService { inner: served };
                    let _ = jetstream_rpc::server::run(&mut service, lane).await;
                });
            }
        }
    });

    sim.client("a", async move {
        connect!(_session, ch);

        // The actor is offered to A at 41, and A takes it.
        assert_eq!(ch.poll(Context::default()).await.unwrap(), Offer::Grant(41));
        ch.acquire(Context::default(), 41).await.unwrap();
        assert_eq!(ch.write(Context::default(), 41).await.unwrap(), 1);

        // A agrees to hand over. The epoch burns immediately — that is what
        // fences A, not the later acknowledgement.
        ch.begin_transfer(Context::default(), 1).await.unwrap();

        // The refusal this whole protocol exists for. A still believes it holds
        // the actor at 41; the registry knows better.
        let fenced = ch
            .write(Context::default(), 41)
            .await
            .expect_err("a write at a burned epoch must be refused");
        assert_eq!(
            fenced.code(),
            Some("FENCED"),
            "the fence must refuse in its own words: {fenced:?}"
        );

        // A is told to stop, and acknowledges at the transfer's epoch.
        assert_eq!(ch.poll(Context::default()).await.unwrap(), Offer::Revoke(42));
        ch.release(Context::default(), 42).await.unwrap();
        Ok(())
    });

    let watched = shared.clone();
    sim.client("b", async move {
        // Wait for the *fact*, not for the clock.
        //
        // This was a fixed 500ms sleep, on the reasoning that turmoil's time is
        // simulated and deterministic — which is true, and is why it would have
        // failed identically every run rather than flakily. But elapsed time is
        // still not a completion barrier: it says a duration passed, not that A
        // acknowledged the revocation, and anything that lengthened A's half of
        // the story would have moved B ahead of it. The condition B actually
        // depends on is observable, so B waits on that instead.
        let mut waited = Duration::ZERO;
        loop {
            let released = watched.get().is_some_and(|r| {
                r.log()
                    .iter()
                    .any(|e| matches!(e, Event::Released { node: 0, new_epoch: 42 }))
            });
            if released {
                break;
            }
            assert!(
                waited < Duration::from_secs(5),
                "A never released the actor, so B has nothing to take"
            );
            tokio::time::sleep(Duration::from_millis(10)).await;
            waited += Duration::from_millis(10);
        }
        connect!(_session, ch);

        assert_eq!(ch.poll(Context::default()).await.unwrap(), Offer::Grant(42));
        ch.acquire(Context::default(), 42).await.unwrap();
        assert_eq!(
            ch.write(Context::default(), 42).await.unwrap(),
            2,
            "B's write is the second to land, which is what the sequence number is for"
        );
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");

    let registry = shared.get().expect("the host built the registry");

    // And the audit log says exactly that happened. The log is what every
    // oracle in `tests/` reads, so a service whose log is right is a service
    // those oracles can be pointed at.
    let log = registry.log();
    assert!(
        log.contains(&Event::Wrote { node: 0, epoch: 41, seq: 1 }),
        "A's write must be recorded: {log:?}"
    );
    assert!(
        log.contains(&Event::Fenced { node: 0, epoch: 41 }),
        "the refusal must be recorded, or no auditor could ever see it: {log:?}"
    );
    assert!(
        log.contains(&Event::EpochBurned {
            from_epoch: 41,
            to_epoch: 42,
            next: 1,
            forced: false
        }),
        "the cooperative burn must be recorded: {log:?}"
    );
    assert!(
        log.contains(&Event::Wrote { node: 1, epoch: 42, seq: 2 }),
        "B's write must be recorded: {log:?}"
    );
}
