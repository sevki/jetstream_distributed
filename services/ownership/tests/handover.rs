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
//! Sequencing is by the simulated clock. turmoil's time is deterministic, so
//! "B starts after A has finished" is a fact about the run rather than a hope
//! about scheduling.

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
use jetstream_distributed_ownership::{
    ownership_protocol::{OwnershipChannel, OwnershipService},
    Event, Offer, Ownership, Registry,
};
use jetstream_rpc::session::{Session, SingleLaneSession};
use turmoil::net::{TcpListener, TcpStream};

const PORT: u16 = 9000;

/// Open a lane to the registry and hand back a channel to call it on.
async fn connect() -> OwnershipChannel {
    let stream = TcpStream::connect(("registry", PORT))
        .await
        .expect("the registry is listening");
    let session = SingleLaneSession::<OwnershipChannel, _, _>::client_io(stream);
    let lane = Session::<OwnershipChannel>::open_lane(&session)
        .await
        .expect("the one lane is available");
    OwnershipChannel::new(64, Box::new(lane))
}

#[test]
fn a_handover_fences_the_outgoing_owner() {
    let mut sim = turmoil::Builder::new().build();

    // The registry is built *inside* the host, because `turmoil::lookup` needs a
    // live simulation to resolve a name and panics without one — every other
    // use of it in this repository is inside a host for the same reason. It is
    // shared back out so the audit log can be read once the run is over.
    let shared: Arc<OnceLock<Registry>> = Arc::new(OnceLock::new());

    let built = shared.clone();
    sim.host("registry", move || {
        let built = built.clone();
        async move {
            // Who is which node, by address. See the crate docs: an address is
            // not a credential, but in a simulated network nothing can spoof
            // one, and the shape — identity arriving with the connection
            // rather than in an argument — is what carries over to TLS.
            let served = built
                .get_or_init(|| {
                    let roster = HashMap::from([
                        (turmoil::lookup("a"), 0u64),
                        (turmoil::lookup("b"), 1u64),
                    ]);
                    Registry::new(roster, 0, 41)
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
        let ch = connect().await;

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

    sim.client("b", async move {
        // After A has finished. Deterministic, because the clock is simulated.
        tokio::time::sleep(Duration::from_millis(500)).await;
        let ch = connect().await;

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
