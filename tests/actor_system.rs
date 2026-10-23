//! `ActorSystem::connect` asks in a fixed order: this node's supervisor first, then
//! discovery, then a dial.
//!
//! The order is the trait's and not an implementation's, so it is tested on an
//! implementation that has nothing else going for it: a supervisor, a table for
//! discovery, and a `dial` that only counts.

use std::collections::HashMap;
use std::num::NonZeroU32;
use std::sync::atomic::{AtomicUsize, Ordering};

use jetstream::prelude::*;
use jetstream_distributed::actor::service::{ActorRef, Capacity, Fence, LocalSupervisor, Supervisor};
use jetstream_distributed::actor::system::ActorSystem;
use jetstream_distributed::id::Id;
use jetstream_distributed::scheduling::discovery::{Discovery, DiscoveryError};
use jetstream_distributed::scheduling::placement::{Placement, PlacementError};

use ping_protocol::{PingChannel, PingService};

const ROOM: Capacity = Capacity::Bounded(NonZeroU32::new(16).unwrap());

const ME: Id = Id(7);
const HERE: ActorRef = ActorRef(Id(1));
const ELSEWHERE: ActorRef = ActorRef(Id(2));
const NOWHERE: ActorRef = ActorRef(Id(3));

/// Where `ELSEWHERE` lives, in the order discovery lists it.
const FIRST: Id = Id(100);
const SECOND: Id = Id(101);

#[service]
trait Ping {
    async fn ping(&self, ctx: Context) -> Result<u64>;
}

struct Pong;

impl Ping for Pong {
    async fn ping(&self, _ctx: Context) -> Result<u64> {
        Ok(42)
    }
}

fn open() -> impl Fence + 'static {
    || true
}

/// A table of where actors live.
struct Table(HashMap<ActorRef, Vec<Id>>);

#[async_trait]
impl Discovery for Table {
    type Resource = ActorRef;
    type Location = Id;

    async fn discover(&self, what: ActorRef) -> std::result::Result<Vec<Id>, DiscoveryError> {
        self.0.get(&what).cloned().ok_or(DiscoveryError::NotFound)
    }
}

/// Places nothing; the trait wants one.
struct Nowhere;

#[async_trait]
impl Placement for Nowhere {
    type Resource = ActorRef;

    async fn place(&mut self, _what: ActorRef) -> std::result::Result<Vec<Id>, PlacementError> {
        Ok(vec![])
    }
}

struct System {
    supervisor: LocalSupervisor,
    table: Table,
    placement: Nowhere,
    dialed: AtomicUsize,
}

impl System {
    fn new() -> Self {
        Self {
            supervisor: LocalSupervisor::new(ME),
            table: Table(HashMap::from([(ELSEWHERE, vec![FIRST, SECOND])])),
            placement: Nowhere,
            dialed: AtomicUsize::new(0),
        }
    }

    fn dials(&self) -> usize {
        self.dialed.load(Ordering::SeqCst)
    }
}

impl ActorSystem for System {
    type Supervisor = LocalSupervisor;
    type Discovery = Table;
    type Placement = Nowhere;

    fn supervisor(&self) -> &LocalSupervisor {
        &self.supervisor
    }

    fn discovery(&self) -> &Table {
        &self.table
    }

    fn placement(&mut self) -> &mut Nowhere {
        &mut self.placement
    }

    async fn dial<P>(&mut self, location: Id, _from: Context) -> Result<Box<dyn ClientTransport<P>>>
    where
        P: Protocol<Error = Error> + 'static,
    {
        self.dialed.fetch_add(1, Ordering::SeqCst);
        Err(Error::new(format!("dialed {location}")))
    }
}

async fn host_here(system: &System) {
    system
        .supervisor()
        .spawn::<PingChannel, _, _>(HERE.0, ROOM, PingService { inner: Pong }, open())
        .await
        .unwrap();
}

/// Run `connect`, expecting it to fail, and say how.
async fn refusal(system: &mut System, actor: ActorRef) -> String {
    match system
        .connect::<PingChannel>(actor, Context::default())
        .await
    {
        Ok(_) => panic!("connected to {actor:?}"),
        Err(why) => why.to_string(),
    }
}

/// An actor running here is reached through its mailbox: no lookup, and nothing is
/// dialed.
#[tokio::test]
async fn a_local_actor_is_reached_without_a_dial() {
    let mut system = System::new();
    host_here(&system).await;

    let transport = system
        .connect::<PingChannel>(HERE, Context::default())
        .await
        .unwrap();
    let ping = PingChannel::new(64, transport);
    ping.negotiate_version(u32::MAX).await.unwrap();

    assert_eq!(ping.ping(Context::default()).await.unwrap(), 42);
    assert_eq!(system.dials(), 0);
}

/// An actor that is not here is looked up, and the first location is the one dialed.
#[tokio::test]
async fn a_remote_actor_is_dialed_at_its_first_location() {
    let mut system = System::new();

    assert_eq!(refusal(&mut system, ELSEWHERE).await, format!("dialed {FIRST}"));
    assert_eq!(system.dials(), 1);
}

/// An actor that is nowhere is refused, and nothing is dialed.
#[tokio::test]
async fn an_actor_that_is_nowhere_is_refused_before_any_dial() {
    let mut system = System::new();

    assert!(refusal(&mut system, NOWHERE).await.contains("actor 3"));
    assert_eq!(system.dials(), 0);
}

/// The supervisor is asked first, but only a **running** actor is answered from it:
/// one that has been drained here falls through to discovery, which is where a
/// caller who was told `FENCED` goes next.
#[tokio::test]
async fn a_drained_actor_is_no_longer_answered_locally() {
    let mut system = System::new();
    host_here(&system).await;
    system.supervisor().drain(HERE.0).await.unwrap();

    // Discovery has never heard of it, so it is refused rather than served.
    assert!(refusal(&mut system, HERE).await.contains("actor 1"));
    assert_eq!(system.dials(), 0);
}
