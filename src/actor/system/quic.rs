#![cfg(all(feature = "service", feature = "quic"))]

use std::collections::HashMap;
use std::time::Duration;

use crate::actor::model::Envelope;
use crate::actor::service::actor_protocol::ActorChannel;
use crate::actor::service::{ActorRef, Closed, LocalSupervisor};
use crate::compute::{Instant, Job, Resources};
use crate::scheduling::discovery::{Discovery, DiscoveryError};
use crate::scheduling::lava::{LifetimePredictor, Scheduler};
use crate::scheduling::placement::{Placement, PlacementError};
use crate::{
    actor::{
        service::{Actor, Receipt, Record, Snapshot},
        system::ActorSystem,
    },
    id::Id,
    ownership::service::Offer,
};
use jetstream::quic::QuicTransport;
use jetstream::{prelude::*, quic};
use url::Url;

pub(crate) struct QuicActorSystem<F, P: LifetimePredictor<F>> {
    supervisor: LocalSupervisor,
    directory: QuicDirectory<F, P>,
    /// Holds the endpoint every connection below was made from, and the
    /// certificates this node presents and trusts. A `quinn` endpoint closes its
    /// connections when its last handle drops, so this lives as long as they do.
    client: quic::Client,
    /// One connection per location, opened on first use and reused while it is
    /// alive. Each call to [`dial`](ActorSystem::dial) opens a stream on it.
    connections: HashMap<Url, quinn::Connection>,
    /// How long one address gets to complete the handshake. QUIC is over UDP, so
    /// an address nobody listens on is not refused: without this, the dial waits
    /// out QUIC's own idle timeout, about thirty seconds.
    connect_timeout: Duration,
}

/// [`QuicActorSystem::connect_timeout`], unless one is given.
const CONNECT_TIMEOUT: Duration = Duration::from_secs(5);

impl<F, P> QuicActorSystem<F, P>
where
    P: LifetimePredictor<F>,
{
    /// A system for the node `me`, hosting nothing, placing with `scheduler`,
    /// and dialing out through `client`.
    pub(crate) fn new(me: Id, scheduler: Scheduler<F, P>, client: quic::Client) -> Self {
        Self {
            supervisor: LocalSupervisor::new(me),
            directory: QuicDirectory::new(scheduler),
            client,
            connections: HashMap::new(),
            connect_timeout: CONNECT_TIMEOUT,
        }
    }

    /// Give each address `timeout` to complete the handshake instead of the
    /// default.
    pub(crate) fn with_connect_timeout(mut self, timeout: Duration) -> Self {
        self.connect_timeout = timeout;
        self
    }

    /// A live connection to `location`: the one already open, or a new one.
    ///
    /// A cached connection that has closed is dropped and replaced rather than
    /// handed out, since opening a stream on it would fail for a reason the
    /// caller could do nothing about. The host in the URL is the name the server's
    /// certificate is checked against; a URL with no port is dialed on 443.
    async fn connection(&mut self, location: &Url) -> Result<quinn::Connection> {
        if let Some(open) = self.connections.get(location) {
            if open.close_reason().is_none() {
                return Ok(open.clone());
            }
            self.connections.remove(location);
        }
        let (host, port) = target(location)?;
        // A name can resolve to several addresses (`localhost` is both `::1` and
        // `127.0.0.1`), and a server listens on one of them: try each, in the order
        // the resolver gave them, and report the last failure if none answers.
        let mut last = Error::new(format!("{location} has no address"));
        let addrs = tokio::net::lookup_host((host, port))
            .await
            .map_err(|why| Error::new(format!("resolving {location}: {why}")))?;
        for addr in addrs {
            let attempt =
                tokio::time::timeout(self.connect_timeout, self.client.connect(addr, host)).await;
            match attempt {
                Ok(Ok(connection)) => {
                    self.connections
                        .insert(location.clone(), connection.clone());
                    return Ok(connection);
                }
                Ok(Err(why)) => {
                    last = Error::new(format!("connecting to {location} at {addr}: {why}"));
                }
                Err(_) => {
                    last = Error::new(format!(
                        "connecting to {location} at {addr}: no answer in {:?}",
                        self.connect_timeout
                    ));
                }
            }
        }
        Err(last)
    }
}

/// The host and port to dial for `location`.
fn target(location: &Url) -> Result<(&str, u16)> {
    let host = location
        .host_str()
        .ok_or_else(|| Error::new(format!("{location} names no host")))?;
    let port = location.port().unwrap_or(443);
    Ok((host, port))
}

/// An actor reached through [`QuicActorSystem::actor`]: the [`Actor`] protocol,
/// spoken over whichever transport `connect` found.
///
/// It is a handle and nothing else, every call is the generated channel's, so it
/// cannot tell a local actor from one on another node. What it does **not** do is
/// pick an actor on a host: the actor's id is not on the wire (#31), so a dial
/// reaches the actor service that host serves, one per host for now.
pub(crate) struct QuicActor {
    channel: ActorChannel,
}

impl Actor for QuicActor {
    async fn poll(&self, ctx: Context) -> Result<Offer> {
        self.channel.poll(ctx).await
    }

    async fn acquire(&self, ctx: Context, epoch: u64) -> Result<()> {
        self.channel.acquire(ctx, epoch).await
    }

    async fn begin_transfer(&self, ctx: Context, to: Id) -> Result<()> {
        self.channel.begin_transfer(ctx, to).await
    }

    async fn release(&self, ctx: Context, epoch: u64) -> Result<()> {
        self.channel.release(ctx, epoch).await
    }

    async fn accept(&self, ctx: Context, epoch: u64, sender: Id, seq: u64) -> Result<Receipt> {
        self.channel.accept(ctx, epoch, sender, seq).await
    }

    async fn state(&self, ctx: Context) -> Result<Snapshot> {
        self.channel.state(ctx).await
    }

    async fn journal(&self, ctx: Context, from: u64, limit: u64) -> Result<Vec<Record>> {
        self.channel.journal(ctx, from, limit).await
    }

    async fn send(&self, ctx: Context, envelope: Envelope) -> Result<()> {
        self.channel.send(ctx, envelope).await
    }

    fn receive(&self, ctx: Context, from: u64) -> Subscription<Envelope, Closed> {
        self.channel.receive(ctx, from)
    }
}

impl<F, P> QuicActorSystem<F, P>
where
    F: Sync + Send + 'static,
    P: LifetimePredictor<F> + Sync + Send,
{
    /// A handle on `actor`: connected as [`ActorSystem::connect`] says, with the
    /// protocol's version negotiated, so the first call is an ordinary one.
    pub(crate) async fn actor(&mut self, actor: ActorRef, from: Context) -> Result<QuicActor> {
        let transport = self.connect::<ActorChannel>(actor, from).await?;
        let channel = ActorChannel::new(64, transport);
        channel.negotiate_version(u32::MAX).await?;
        Ok(QuicActor { channel })
    }
}

/// Where actors live and where new ones go: a [`Scheduler`] that chooses a host,
/// and the address of every host it can choose.
///
/// A job is an actor here, and its [`Id`] is the actor's. Placing one records the
/// address of the host the scheduler chose, which is what [`Discovery`] then
/// answers. That record is a cache of the placement and is not kept in step with
/// it: an actor that has exited or moved stays where it was put until it is
/// placed again, and a caller that goes to the old address is answered `FENCED`.
pub struct QuicDirectory<F, P: LifetimePredictor<F>> {
    /// How to reach each host: what [`Discovery`] returns for an actor placed on it.
    hosts: HashMap<Id, url::Url>,
    placed_actors: HashMap<ActorRef, url::Url>,
    scheduler: Scheduler<F, P>,
}

impl<F, P> QuicDirectory<F, P>
where
    P: LifetimePredictor<F>,
{
    pub fn new(scheduler: Scheduler<F, P>) -> Self {
        Self {
            hosts: HashMap::default(),
            placed_actors: HashMap::default(),
            scheduler,
        }
    }

    /// A host that jobs can be placed on, and where it is reached.
    ///
    /// It is both at once because a host the scheduler chooses but nobody can
    /// reach would take a job that discovery cannot find. Refused as the
    /// scheduler refuses a host: one with no CPU or no memory, or an id it
    /// already has.
    pub fn add_host(
        &mut self,
        id: Id,
        capacity: Resources,
        at: url::Url,
    ) -> std::result::Result<(), PlacementError> {
        self.scheduler.add_host(id, capacity)?;
        self.hosts.insert(id, at);
        Ok(())
    }
}

#[async_trait]
impl<F, P> Discovery for QuicDirectory<F, P>
where
    F: Sync + Send + 'static,
    P: LifetimePredictor<F> + Sync,
{
    type Resource = ActorRef;
    type Location = url::Url;

    async fn discover(
        &self,
        what: Self::Resource,
    ) -> std::result::Result<Vec<Self::Location>, DiscoveryError> {
        self.placed_actors
            .get(&what)
            .cloned()
            .ok_or(DiscoveryError::NotFound)
            .map(|url| vec![url])
    }
}

#[async_trait]
impl<F, P: LifetimePredictor<F>> Placement for QuicDirectory<F, P>
where
    F: Sync + Send + 'static,
    Self: Send + Sync,
{
    type Resource = Job<F>;

    /// The host the scheduler chose, and from then on [`Discovery`] answers its
    /// address for the job's actor.
    ///
    /// [`PlacementError::UnknownHost`] if the scheduler chose a host that has no
    /// address (one it was given before the directory was); the job is taken back
    /// out of the scheduler, so it is not left placed where nobody can reach it.
    async fn place(
        &mut self,
        what: Self::Resource,
    ) -> std::result::Result<Vec<Id>, PlacementError> {
        let actor = ActorRef(what.id);
        let host = self.scheduler.place(what, Instant::now())?;
        let Some(at) = self.hosts.get(&host) else {
            let _ = self.scheduler.remove(actor.0, Instant::now());
            return Err(PlacementError::UnknownHost);
        };
        self.placed_actors.insert(actor, at.clone());
        Ok(vec![host])
    }
}

impl<F, P> ActorSystem for QuicActorSystem<F, P>
where
    F: Sync + Send + 'static,
    P: LifetimePredictor<F> + Sync + Send,
{
    type Supervisor = LocalSupervisor;
    type Discovery = QuicDirectory<F, P>;
    type Placement = QuicDirectory<F, P>;

    fn supervisor(&self) -> &LocalSupervisor {
        &self.supervisor
    }

    fn discovery(&self) -> &QuicDirectory<F, P> {
        &self.directory
    }

    fn placement(&mut self) -> &mut QuicDirectory<F, P> {
        &mut self.directory
    }

    /// A stream to `location`, on the connection to it, which is opened first if
    /// there is none.
    ///
    /// `_from` is not used: who this node is to the server is the certificate
    /// `client` was built with, not something a caller chooses per call.
    async fn dial<Q>(
        &mut self,
        location: url::Url,
        _from: Context,
    ) -> Result<Box<dyn ClientTransport<Q>>>
    where
        Q: Protocol<Error = Error> + 'static,
    {
        let connection = self.connection(&location).await?;
        let streams = connection
            .open_bi()
            .await
            .map_err(|why| Error::new(format!("opening a stream to {location}: {why}")))?;
        Ok(Box::new(QuicTransport::<Q>::from(streams)))
    }
}

#[cfg(test)]
mod tests {
    //! The dial, over a real QUIC handshake on the loopback interface, with the
    //! certificates Jetstream's own tests use (`vendor/jetstream/certs`).

    use std::net::{SocketAddr, UdpSocket};
    use std::path::Path;
    use std::sync::Arc;

    use jetstream::quic::{QuicRouter, QuicRouterHandler, Server};
    use rustls::pki_types::{CertificateDer, PrivateKeyDer};

    use crate::actor::model::Envelope;
    use crate::actor::service::Closed;
    use crate::actor::service::actor_protocol::ActorChannel;
    use crate::compute::{Cpu, Memory};
    use crate::scheduling::lava::{EmpiricalLifetime, EmpiricalPredictor};

    use super::*;
    use ping_protocol::{PingChannel, PingService};

    #[service]
    trait Ping {
        async fn ping(&self, ctx: Context) -> Result<u64>;
    }

    #[derive(Clone)]
    struct Pong;

    impl Ping for Pong {
        async fn ping(&self, _ctx: Context) -> Result<u64> {
            Ok(42)
        }
    }

    const CERTS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/vendor/jetstream/certs");

    fn certs(file: &str) -> Vec<CertificateDer<'static>> {
        let data = std::fs::read(Path::new(CERTS).join(file)).expect("a certificate");
        rustls_pemfile::certs(&mut &*data)
            .filter_map(|cert| cert.ok())
            .collect()
    }

    fn key(file: &str) -> PrivateKeyDer<'static> {
        let data = std::fs::read(Path::new(CERTS).join(file)).expect("a key");
        rustls_pemfile::private_key(&mut &*data)
            .expect("a parseable key")
            .expect("a key in the file")
    }

    /// An address nothing is listening on yet.
    fn free_address() -> SocketAddr {
        UdpSocket::bind("127.0.0.1:0")
            .and_then(|socket| socket.local_addr())
            .expect("a free port")
    }

    /// Serve `Ping` at `addr`, on the ALPN every Jetstream router speaks.
    fn serve(addr: SocketAddr) -> tokio::task::JoinHandle<()> {
        serve_with(
            addr,
            jetstream_rpc::Router::new()
                .with_handler(ping_protocol::PROTOCOL_NAME, PingService { inner: Pong }),
        )
    }

    /// Serve the actor protocol at `addr`, answered by [`Stub`].
    fn serve_actor(addr: SocketAddr) -> tokio::task::JoinHandle<()> {
        serve_with(
            addr,
            jetstream_rpc::Router::new().with_handler(
                crate::actor::service::actor_protocol::PROTOCOL_NAME,
                crate::actor::service::actor_protocol::ActorService { inner: Stub },
            ),
        )
    }

    fn serve_with(addr: SocketAddr, rpc: jetstream_rpc::Router) -> tokio::task::JoinHandle<()> {
        rustls::crypto::ring::default_provider()
            .install_default()
            .ok();
        let service = rpc;
        let mut router = QuicRouter::new();
        router.register(Arc::new(QuicRouterHandler::new(Arc::new(service))));
        let server = Server::new_with_addr(
            vec![certs("server.pem").pop().unwrap()],
            key("server.key"),
            addr,
            router,
        );
        tokio::spawn(async move { server.run().await })
    }

    fn system() -> QuicActorSystem<EmpiricalLifetime, EmpiricalPredictor> {
        rustls::crypto::ring::default_provider()
            .install_default()
            .ok();
        let client = quic::Client::new(
            certs("ca.pem").pop().unwrap(),
            vec![b"jetstream".to_vec()],
            "0.0.0.0:0".parse().unwrap(),
        )
        .expect("a client");
        QuicActorSystem::new(Id::from(1), Scheduler::new(EmpiricalPredictor), client)
    }

    fn url(addr: SocketAddr) -> Url {
        Url::parse(&format!("quic://localhost:{}", addr.port())).unwrap()
    }

    async fn ping(
        system: &mut QuicActorSystem<EmpiricalLifetime, EmpiricalPredictor>,
        at: Url,
    ) -> Result<u64> {
        let transport = system.dial::<PingChannel>(at, Context::default()).await?;
        let channel = PingChannel::new(1, transport);
        channel.negotiate_version(u32::MAX).await?;
        channel.ping(Context::default()).await
    }

    #[tokio::test]
    async fn an_actor_that_is_nowhere_cannot_be_reached() {
        let mut system = system();
        let Err(why) = system
            .connect::<ActorChannel>(ActorRef(Id::from(7)), Context::default())
            .await
        else {
            panic!("an actor nobody hosts and nobody knows was reached");
        };
        assert!(why.to_string().contains("actor 7"), "{why}");
    }

    /// A location with no host is refused before anything is sent; one with no
    /// port is dialed on 443.
    #[test]
    fn a_location_needs_a_host_and_defaults_its_port() {
        let no_port = Url::parse("quic://localhost").unwrap();
        assert_eq!(target(&no_port).unwrap(), ("localhost", 443));
        let no_host = Url::parse("unix:/run/actor").unwrap();
        assert!(
            target(&no_host)
                .unwrap_err()
                .to_string()
                .contains("no host")
        );
        let both = Url::parse("quic://example.com:4433").unwrap();
        assert_eq!(target(&both).unwrap(), ("example.com", 4433));
    }

    /// The first dial connects, and a call goes through the stream it opens.
    #[tokio::test]
    async fn a_dial_reaches_a_server() {
        let addr = free_address();
        let server = serve(addr);
        let mut system = system();

        assert_eq!(ping(&mut system, url(addr)).await.unwrap(), 42);
        assert_eq!(system.connections.len(), 1);
        server.abort();
    }

    /// A second dial to the same place is a new stream on the same connection, not
    /// a new connection.
    #[tokio::test]
    async fn a_second_dial_reuses_the_connection() {
        let addr = free_address();
        let server = serve(addr);
        let mut system = system();

        assert_eq!(ping(&mut system, url(addr)).await.unwrap(), 42);
        let first = system.connections[&url(addr)].stable_id();
        assert_eq!(ping(&mut system, url(addr)).await.unwrap(), 42);
        assert_eq!(system.connections[&url(addr)].stable_id(), first);
        server.abort();
    }

    /// A connection that has closed is replaced, not handed out again.
    #[tokio::test]
    async fn a_closed_connection_is_replaced() {
        let addr = free_address();
        let server = serve(addr);
        let mut system = system();

        assert_eq!(ping(&mut system, url(addr)).await.unwrap(), 42);
        let first = system.connections[&url(addr)].clone();
        first.close(0u32.into(), b"test");
        assert!(first.close_reason().is_some());

        assert_eq!(ping(&mut system, url(addr)).await.unwrap(), 42);
        assert_ne!(
            system.connections[&url(addr)].stable_id(),
            first.stable_id()
        );
        server.abort();
    }

    /// Nobody is listening: UDP does not refuse, so it is the timeout that ends the
    /// dial. The error says where it tried, and nothing is cached.
    #[tokio::test]
    async fn a_dial_to_nobody_times_out_and_caches_nothing() {
        let mut system = system().with_connect_timeout(Duration::from_millis(300));
        let at = url(free_address());

        let started = std::time::Instant::now();
        let why = ping(&mut system, at.clone()).await.unwrap_err().to_string();
        assert!(why.contains(&at.to_string()), "{why}");
        assert!(why.contains("no answer"), "{why}");
        assert!(
            started.elapsed() < Duration::from_secs(5),
            "{:?}",
            started.elapsed()
        );
        assert!(system.connections.is_empty());
    }

    /// An actor that answers each call with something that depends on every
    /// argument it was given, so a test sees a call arrive intact or not at all.
    #[derive(Clone)]
    struct Stub;

    impl Actor for Stub {
        async fn poll(&self, _ctx: Context) -> Result<Offer> {
            Ok(Offer::Grant(3))
        }

        async fn acquire(&self, _ctx: Context, epoch: u64) -> Result<()> {
            (epoch == 9)
                .then_some(())
                .ok_or_else(|| Error::new(format!("acquire at {epoch}")))
        }

        async fn begin_transfer(&self, _ctx: Context, to: Id) -> Result<()> {
            (to == Id::from(5))
                .then_some(())
                .ok_or_else(|| Error::new(format!("begin_transfer to {to}")))
        }

        async fn release(&self, _ctx: Context, epoch: u64) -> Result<()> {
            (epoch == 11)
                .then_some(())
                .ok_or_else(|| Error::new(format!("release at {epoch}")))
        }

        async fn accept(&self, _ctx: Context, epoch: u64, sender: Id, seq: u64) -> Result<Receipt> {
            Ok(Receipt {
                index: seq,
                state: u128::from(sender) as u64 * 100 + epoch,
            })
        }

        async fn state(&self, _ctx: Context) -> Result<Snapshot> {
            Ok(Snapshot { len: 2, state: 7 })
        }

        async fn journal(&self, _ctx: Context, from: u64, limit: u64) -> Result<Vec<Record>> {
            Ok(vec![Record {
                sender: Id::from(1),
                seq: from,
                body: vec![limit as u8],
                host: Id::from(2),
                epoch: 3,
            }])
        }

        async fn send(&self, _ctx: Context, envelope: Envelope) -> Result<()> {
            (envelope.sender == Id::from(6) && envelope.seq == 3 && envelope.body == [41, 42])
                .then_some(())
                .ok_or_else(|| Error::new(format!("send {envelope:?}")))
        }

        #[doc = " Streaming: many `Event`s share the request\'s tag, and the end"]
        #[doc = " carries a `Closed`."]
        fn receive(&self, _ctx: Context, _from: u64) -> Subscription<Envelope, Closed> {
            todo!()
        }
    }

    /// A job for `actor`, small enough for any host `roomy` makes.
    fn job(actor: ActorRef) -> Job<EmpiricalLifetime> {
        Job {
            id: actor.0,
            resources: Resources {
                cpu: Cpu::cores(1),
                memory: Memory::mib(64),
            },
            started_at: Instant::EPOCH,
            features: EmpiricalLifetime::new(
                vec![Duration::from_secs(60)],
                Duration::from_secs(3600),
            )
            .unwrap(),
        }
    }

    fn roomy() -> Resources {
        Resources {
            cpu: Cpu::cores(8),
            memory: Memory::mib(1024),
        }
    }

    /// The host `actor` is placed on in [`system_that_knows`].
    const HOST: Id = Id(2);

    /// A system that has placed `actor` on a host at `at`, the way a caller would:
    /// by adding the host and asking the directory to place it.
    async fn system_that_knows(
        actor: ActorRef,
        at: Url,
    ) -> QuicActorSystem<EmpiricalLifetime, EmpiricalPredictor> {
        let mut system = system();
        system.directory.add_host(HOST, roomy(), at).unwrap();
        assert_eq!(
            system.placement().place(job(actor)).await.unwrap(),
            vec![HOST]
        );
        system
    }

    /// **Placing an actor is what lets discovery find it**, at the address of the
    /// host the scheduler chose and not before.
    #[tokio::test]
    async fn a_placed_actor_is_found_at_its_hosts_address() {
        let actor = ActorRef(Id::from(7));
        let at = Url::parse("quic://host-2.example:4433").unwrap();
        let mut system = system();
        system
            .directory
            .add_host(HOST, roomy(), at.clone())
            .unwrap();

        assert_eq!(
            system.discovery().discover(actor).await,
            Err(DiscoveryError::NotFound),
            "nothing is placed yet"
        );
        assert_eq!(
            system.placement().place(job(actor)).await.unwrap(),
            vec![HOST]
        );
        assert_eq!(system.discovery().discover(actor).await, Ok(vec![at]));
        assert_eq!(
            system.discovery().discover(ActorRef(Id::from(8))).await,
            Err(DiscoveryError::NotFound),
            "only the placed actor is found"
        );
    }

    /// A host that is added with an address is the only kind placement may choose:
    /// one the scheduler holds without an address is refused, and the job is not
    /// left placed on it.
    #[tokio::test]
    async fn a_host_nobody_can_reach_is_not_placed_on() {
        let actor = ActorRef(Id::from(7));
        let mut scheduler = Scheduler::new(EmpiricalPredictor);
        scheduler.add_host(HOST, roomy()).unwrap();
        let mut directory = QuicDirectory::new(scheduler);

        assert_eq!(
            directory.place(job(actor)).await,
            Err(PlacementError::UnknownHost)
        );
        assert_eq!(directory.scheduler.location(actor.0), None, "taken back");
        assert_eq!(
            directory.discover(actor).await,
            Err(DiscoveryError::NotFound)
        );
    }

    /// Every method of the protocol reaches the server with its arguments, and
    /// brings the server's answer back, through discovery, a dial and a negotiated
    /// channel.
    #[tokio::test]
    async fn an_actor_is_called_across_the_connection() {
        let addr = free_address();
        let server = serve_actor(addr);
        let actor = ActorRef(Id::from(7));
        let mut system = system_that_knows(actor, url(addr)).await;

        let remote = system.actor(actor, Context::default()).await.unwrap();
        let ctx = Context::default;

        assert_eq!(remote.poll(ctx()).await.unwrap(), Offer::Grant(3));
        remote.acquire(ctx(), 9).await.unwrap();
        remote.begin_transfer(ctx(), Id::from(5)).await.unwrap();
        remote.release(ctx(), 11).await.unwrap();
        let envelope = Envelope {
            sender: Id::from(6),
            seq: 3,
            body: vec![41, 42],
        };
        remote.send(ctx(), envelope.clone()).await.unwrap();
        assert!(
            remote
                .send(ctx(), Envelope { seq: 4, ..envelope })
                .await
                .is_err(),
            "the server saw the envelope it was given, not another"
        );
        assert_eq!(
            remote.accept(ctx(), 4, Id::from(6), 8).await.unwrap(),
            Receipt {
                index: 8,
                state: 604
            }
        );
        assert_eq!(
            remote.state(ctx()).await.unwrap(),
            Snapshot { len: 2, state: 7 }
        );
        assert_eq!(
            remote.journal(ctx(), 5, 6).await.unwrap(),
            vec![Record {
                sender: Id::from(1),
                seq: 5,
                body: vec![6],
                host: Id::from(2),
                epoch: 3
            }]
        );
        server.abort();
    }

    /// The server's refusal arrives as an error, with what it said.
    #[tokio::test]
    async fn a_refusal_crosses_the_connection() {
        let addr = free_address();
        let server = serve_actor(addr);
        let actor = ActorRef(Id::from(7));
        let mut system = system_that_knows(actor, url(addr)).await;

        let remote = system.actor(actor, Context::default()).await.unwrap();
        let why = remote
            .acquire(Context::default(), 8)
            .await
            .unwrap_err()
            .to_string();

        assert!(why.contains("acquire at 8"), "{why}");
        server.abort();
    }
}
