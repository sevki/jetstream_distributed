//! Reaching a [`Host`] over any byte stream.
//!
//! The host is reached the way any peer reaches it: a client channel generated
//! by `#[service]`, a session over a byte stream, and the generated server
//! running on the far end. Nothing is called directly.
//!
//! [`Host::serve`] and [`Connection::new`] are the two halves, and they
//! take any `AsyncRead + AsyncWrite` stream — TCP, QUIC, turmoil, an iroh stream
//! pair. The one thing a stream may not be able to say is who is on the other
//! end, so `serve` takes it as the peer `Context`: an accept loop reads it off
//! the socket, a TLS adapter supplies the identity its handshake established.
//! The host believes it, so it must come from the transport, never from the peer.
//!
//! That is the byte-stream transport. The actor's own transport, a mailbox, is
//! [`super::session`].
//!
//! [`Host::pipe`] is the same wiring over an in-memory stream, which is what lets
//! the actor be exercised through Jetstream without a network. There the caller
//! names the peer, so it is for tests and examples, not a deployment.

use tokio::io::{AsyncRead, AsyncWrite};

use super::actor_protocol::{ActorChannel, ActorService};
use super::Host;
use jetstream::prelude::jetstream_rpc::context::{Context, RemoteAddr};
use jetstream::prelude::jetstream_rpc::session::{Session, SingleLaneSession};
use jetstream::prelude::*;

/// Room for in-flight bytes in each direction.
const PIPE: usize = 64 * 1024;
/// Frames a client lane holds before applying backpressure.
const LANE: u16 = 64;

impl Host {
    /// Serve one connection over `io` until the peer goes away.
    ///
    /// `peer` is who is on the other end, as the transport established it: a
    /// TLS adapter passes the identity its handshake produced, an accept loop
    /// over TCP or turmoil the connection's remote address. The host believes
    /// it, so it must come from the transport and never from the peer.
    pub async fn serve<T>(&self, io: T, peer: Context)
    where
        T: AsyncRead + AsyncWrite + Send + Sync + Unpin + 'static,
    {
        let session = SingleLaneSession::<ActorChannel, _, _>::service_io_with_context(io, peer);
        let Ok(lane) = Session::<ActorChannel>::accept_lane(&session).await else {
            return;
        };
        let mut service = ActorService {
            inner: self.clone(),
        };
        let _ = jetstream::prelude::jetstream_rpc::server::run(&mut service, lane).await;
    }

    /// A client channel to this host, connected as the node at `peer` over an
    /// in-memory pipe.
    ///
    /// The host serves the connection on a spawned task, and stops when the
    /// channel is dropped. Must be called inside a tokio runtime.
    pub async fn pipe(&self, peer: RemoteAddr) -> Connection {
        let (client_io, server_io) = tokio::io::duplex(PIPE);
        let host = self.clone();
        tokio::spawn(async move {
            host.serve(server_io, Context::new(Some(peer), None)).await;
        });
        Connection::new(client_io)
            .await
            .expect("an in-memory pipe has its one lane and the host speaks this version")
    }
}

/// A client channel, and the session that keeps it open.
///
/// The session has to outlive the channel: dropping a `SingleLaneSession`
/// cancels its lane, so a channel built from the lane alone would stop working
/// the moment the session went out of scope.
pub struct Connection {
    channel: ActorChannel,
    _session: Box<dyn std::any::Any + Send + Sync>,
}

impl Connection {
    /// A client over any byte stream: TCP, QUIC, turmoil, an iroh stream pair.
    /// Must be called inside a tokio runtime.
    ///
    /// Fails if the stream cannot give a lane or the peer will not agree on a
    /// version — an ordinary thing for a network connection to do, so it is an
    /// error for the caller to handle or retry, not a panic.
    pub async fn new<T>(io: T) -> Result<Connection>
    where
        T: AsyncRead + AsyncWrite + Send + Sync + Unpin + 'static,
    {
        let session = SingleLaneSession::<ActorChannel, _, _>::client_io(io);
        let lane = Session::<ActorChannel>::open_lane(&session).await?;
        let channel = ActorChannel::new(LANE, Box::new(lane));
        channel.negotiate_version(u32::MAX).await?;
        Ok(Connection {
            channel,
            _session: Box::new(session),
        })
    }
}

impl std::ops::Deref for Connection {
    type Target = ActorChannel;
    fn deref(&self) -> &ActorChannel {
        &self.channel
    }
}
