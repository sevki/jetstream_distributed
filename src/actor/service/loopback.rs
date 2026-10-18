//! An in-process Jetstream connection to a [`Host`].
//!
//! The host is reached the way any peer reaches it: a client channel generated
//! by `#[service]`, a session over a byte stream, and the generated server
//! running on the far end. Nothing is called directly. What differs from a
//! socket is only the stream — an in-memory pipe — so the one thing the pipe
//! cannot say, who is on the other end, is supplied by the caller as the peer
//! `Context`, which is what a TLS adapter does with the identity its handshake
//! established.
//!
//! This is what lets the actor be exercised through Jetstream without a network,
//! and it is the same wiring a transport would use.

use std::net::IpAddr;

use super::actor_protocol::{ActorChannel, ActorService};
use super::Host;
use jetstream::prelude::jetstream_rpc::context::{Context, RemoteAddr};
use jetstream::prelude::jetstream_rpc::session::{Session, SingleLaneSession};

/// Room for in-flight bytes in each direction.
const PIPE: usize = 64 * 1024;
/// Frames a client lane holds before applying backpressure.
const LANE: u16 = 64;

impl Host {
    /// A client channel to this host, connected as the node at `peer`.
    ///
    /// The host serves the connection on a spawned task, and stops when the
    /// channel and its session are dropped. Must be called inside a tokio
    /// runtime.
    pub async fn connect(&self, peer: IpAddr) -> Connection {
        let (client_io, server_io) = tokio::io::duplex(PIPE);
        let host = self.clone();
        tokio::spawn(async move {
            let session = SingleLaneSession::<ActorChannel, _, _>::service_io_with_context(
                server_io,
                Context::new(Some(RemoteAddr::IpAddr(peer)), None),
            );
            let Ok(lane) = Session::<ActorChannel>::accept_lane(&session).await else {
                return;
            };
            let mut service = ActorService { inner: host };
            let _ = jetstream::prelude::jetstream_rpc::server::run(&mut service, lane).await;
        });

        let session = SingleLaneSession::<ActorChannel, _, _>::client_io(client_io);
        let lane = Session::<ActorChannel>::open_lane(&session)
            .await
            .expect("an in-memory session has its one lane");
        let channel = ActorChannel::new(LANE, Box::new(lane));
        channel
            .negotiate_version(u32::MAX)
            .await
            .expect("the host speaks this version");
        Connection {
            channel,
            _session: Box::new(session),
        }
    }
}

/// A connected client: the channel, and the session that keeps it open.
pub struct Connection {
    channel: ActorChannel,
    _session: Box<dyn std::any::Any + Send + Sync>,
}

impl std::ops::Deref for Connection {
    type Target = ActorChannel;
    fn deref(&self) -> &ActorChannel {
        &self.channel
    }
}
