//! A lane for one actor: the id it opens with, and the forwarding that follows.
//!
//! A connection to a host is shared by every actor on it, and nothing a transport
//! knows when a lane opens (the connection's ALPN, the peer's certificate) says
//! which of them the lane is for. So **the first thing on a lane is the actor's
//! [`Id`]**, written once; everything after it is the actor's own protocol, version
//! negotiation included. The id is the supervisor's key, so the actor never sees
//! it, and it is on the lane and not in each message because a lane is one
//! caller's ordered channel into one mailbox: it keeps that order and names that
//! mailbox once.
//!
//! This file is the transport-independent half. [`write_attach`] and
//! [`read_attach`] are the preamble, over any byte stream; [`bridge`] connects the
//! lane the callee accepted to the transport a [`Supervisor`](super::Supervisor)
//! returned for that id. What opens and accepts the lane is the transport's.
//!
//! The lane is the caller's handle. When it ends, so does its place in line, and
//! nothing here reconnects: a call in flight may or may not have run, and quietly
//! sending it again on a new lane would also reorder it behind later ones.

use std::io;

use jetstream::prelude::futures::{SinkExt, StreamExt, future, Sink, Stream};
use jetstream::prelude::*;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};

use crate::id::Id;

/// Open a lane for `actor`: write its id, which must be the first thing sent.
pub async fn write_attach<W>(lane: &mut W, actor: Id) -> io::Result<()>
where
    W: AsyncWrite + Unpin,
{
    let mut bytes = Vec::new();
    actor.encode(&mut bytes)?;
    lane.write_all(&bytes).await
}

/// Read the id a lane was opened for. Consumes exactly the preamble, so what
/// follows on `lane` is the actor's protocol.
pub async fn read_attach<R>(lane: &mut R) -> io::Result<Id>
where
    R: AsyncRead + Unpin,
{
    let mut bytes = vec![0u8; usize::try_from(Id::from(0).byte_size()).expect("an id is small")];
    lane.read_exact(&mut bytes).await?;
    Id::decode(&mut bytes.as_slice())
}

/// Forward `lane`, in both directions, to and from `transport` until either side
/// ends.
///
/// Frames pass through unchanged, tags included: the tags belong to the caller's
/// channel, and the mailbox's session answers them as they came. When the caller
/// closes its half the transport is closed after what it sent, so the actor
/// answers everything already queued before the lane ends.
pub async fn bridge<P, L, T>(lane: L, transport: T) -> Result<()>
where
    P: Protocol<Error = Error>,
    L: Stream<Item = Result<Frame<P::Request>>>
        + Sink<Frame<P::Response>, Error = Error>
        + Unpin,
    T: Stream<Item = Result<Frame<P::Response>>>
        + Sink<Frame<P::Request>, Error = Error>
        + Unpin,
{
    let (mut to_caller, mut from_caller) = lane.split();
    let (mut to_actor, mut from_actor) = transport.split();

    let requests = async {
        while let Some(frame) = from_caller.next().await {
            to_actor.send(frame?).await?;
        }
        to_actor.close().await
    };
    let responses = async {
        while let Some(frame) = from_actor.next().await {
            to_caller.send(frame?).await?;
        }
        to_caller.close().await
    };

    future::try_join(requests, responses).await.map(|_| ())
}
