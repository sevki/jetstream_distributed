//! The headline story, in process: a handover that fences the outgoing owner.
//!
//! `A` owns an actor at epoch 41 and writes. `A` agrees to hand it to `B`, which burns
//! the epoch at once. `A`, not yet knowing, writes again at 41 and is **fenced**. `B`
//! takes the actor at 42 and writes.
//!
//! That one refusal is what the protocol exists for. The registry is called directly
//! here, with no network, so the example is the shortest possible account of it. Over a
//! real connection nothing changes except where the caller's identity comes from:
//! [`Context::remote`] is filled in by the transport, never taken from an argument, and
//! the registry maps that address to a node through a roster fixed at construction.
//!
//! Run it with `cargo run --example ownership_handover`.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;

use jetstream::prelude::jetstream_rpc::context::{Context, RemoteAddr};
use jetstream::prelude::*;
use jetstream_distributed::id::Id;
use jetstream_distributed::ownership::service::{MemoryFloor, Offer, Ownership, Registry};

const ADDR_A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
const ADDR_B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));
const A: Id = Id(0);
const B: Id = Id(1);

/// The context a call from `addr` carries: what a transport would fill in.
fn from(addr: IpAddr) -> Context {
    Context::new(Some(RemoteAddr::IpAddr(addr)), None)
}

#[tokio::main]
async fn main() -> Result<()> {
    // Who is which node, by address, and where the epochs start. The floor is a
    // durable record of the highest epoch the registry has used, which is what keeps
    // a restart from rewinding the actor; seeding it at 40 makes the first epoch 41.
    let roster = HashMap::from([(ADDR_A, A), (ADDR_B, B)]);
    let registry = Registry::new(roster, A, Arc::new(MemoryFloor::at(40)))?;

    // The actor is offered to A at 41, and A takes it and writes.
    assert_eq!(registry.poll(from(ADDR_A)).await?, Offer::Grant(41));
    registry.acquire(from(ADDR_A), 41).await?;
    assert_eq!(registry.write(from(ADDR_A), 41).await?, 1);
    println!("A owns the actor at epoch 41 and wrote");

    // A agrees to hand it to B. The epoch is burned from this moment, so A is already
    // fenced out, whether or not it has been told.
    registry.begin_transfer(from(ADDR_A), B).await?;

    // The refusal this protocol exists for. A still believes it holds epoch 41; the
    // registry knows better, and says so in its own word.
    let fenced = registry.write(from(ADDR_A), 41).await.unwrap_err();
    assert_eq!(fenced.code(), Some("FENCED"));
    println!("A's write at the burned epoch 41 was refused: FENCED");

    // A is told to stop, and acknowledges at the transfer's epoch.
    assert_eq!(registry.poll(from(ADDR_A)).await?, Offer::Revoke(42));
    registry.release(from(ADDR_A), 42).await?;

    // Only now is the actor on offer to B, at the new epoch.
    assert_eq!(registry.poll(from(ADDR_B)).await?, Offer::Grant(42));
    registry.acquire(from(ADDR_B), 42).await?;
    assert_eq!(registry.write(from(ADDR_B), 42).await?, 2);
    println!("B took the actor at epoch 42 and wrote");

    // The audit log is what the test oracles read, and it records the refusal.
    for event in registry.log() {
        println!("  {event:?}");
    }
    Ok(())
}
