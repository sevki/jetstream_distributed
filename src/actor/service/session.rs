//! Calling an actor through its mailbox, without the caller knowing.
//!
//! A [`Session`] is a [`ClientTransport`]: a `Sink` of requests and a `Stream` of
//! responses, which is all a generated channel asks of what it sits on. Put one
//! under `XChannel::new` and the channel is a client of whatever [`serve`] is
//! running on the other end of the mailbox, and `self.b.b(ctx).await` is the same
//! call it would be on the implementation itself. The mailbox is not visible in
//! any signature; it is what the call goes through.
//!
//! ```text
//!   caller ── XChannel ── Session ──▶ Mailbox ──▶ serve ── XService ── impl
//!                            ◀── reply ─────────────────────┘
//! ```
//!
//! # The sender's steps are the sink's
//!
//! `poll_ready` reserves a slot ([`Mailbox::poll_reserve`]) and `start_send` is
//! [`Permit::enqueue`]: the request is on the queue. `poll_flush`
//! is the rest of the sender's operation — [`Mailbox::set_state`] and
//! [`Mailbox::schedule`] — which is where the drain is woken. They are separate
//! methods because they are separate steps in the model, and the protocol's bug
//! lives between them. A request that is sent and never flushed is enqueued and
//! never announced; a generated channel flushes every request it sends.
//!
//! # Who is calling
//!
//! The drain reads the sender's identity off the delivery, not the lane: a
//! mailbox has many senders and one drain, and [`Server::rpc`] takes the
//! `Context` per call. A session is built with the caller's `Context`, so it is
//! supplied by whoever builds the session — the same assumption the rest of the
//! service makes, that an identity comes from the transport and not from the
//! peer.
//!
//! # What is not here
//!
//! * **The ownership fence.** `serve` hands each request to the service in the
//!   order the mailbox gives it; it does not yet check the epoch the actor is
//!   hosted at. The fence belongs around [`Server::rpc`].
//! * **Subscriptions.** Streaming methods, and cancelling them, are served by
//!   `jetstream_rpc::server::run` on a lane, and a mailbox delivers one request
//!   and takes one response.
//! * **Backpressure on replies.** The mailbox is bounded, and a full one makes
//!   `poll_ready` wait; the reply channel back to each session is not.

use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::task::{self, Poll};

use jetstream::prelude::futures::{Sink, Stream};
use jetstream::prelude::jetstream_rpc::context::Context;
use jetstream::prelude::jetstream_rpc::server::Server;
use jetstream::prelude::*;
use tokio::sync::mpsc;

use super::{Mailbox, Permit};

/// One request, on its way to the actor: who sent it, what it says, and where
/// the answer goes.
pub struct Delivery<P: Protocol> {
    from: Context,
    frame: Frame<P::Request>,
    reply: mpsc::UnboundedSender<Result<Frame<P::Response>>>,
}

/// A caller's end of a mailbox: a [`ClientTransport`] whose requests are queued
/// for [`serve`] and whose responses are the ones addressed to this session.
pub struct Session<P: Protocol> {
    mailbox: Mailbox<Delivery<P>>,
    from: Context,
    reply: mpsc::UnboundedSender<Result<Frame<P::Response>>>,
    replies: mpsc::UnboundedReceiver<Result<Frame<P::Response>>>,
    /// Requests enqueued whose `set_state` and `schedule` have not run.
    unannounced: AtomicU64,
    /// The slot `poll_ready` reserved for the request `start_send` is about to
    /// enqueue.
    permit: Option<Permit<Delivery<P>>>,
}

impl<P: Protocol> Session<P> {
    /// A session on `mailbox`, calling as `from`.
    pub fn new(mailbox: Mailbox<Delivery<P>>, from: Context) -> Self {
        let (reply, replies) = mpsc::unbounded_channel();
        Session {
            mailbox,
            from,
            reply,
            replies,
            unannounced: AtomicU64::new(0),
            permit: None,
        }
    }

    /// A handle that closes this session when it is dropped.
    ///
    /// **Keep it as long as the channel built on the session, and drop it with
    /// the channel.** A generated channel hands its transport to Jetstream's
    /// multiplexer, which runs three tasks that hold one another up: the one
    /// reading responses ends only when the transport's stream does, and nothing
    /// else lets go of the channel's send queue first. Over a socket the peer
    /// closing ends the stream. A session has no peer, and holds the sender its
    /// own stream reads from, so its stream never ends on its own: a discarded
    /// channel would leave its tasks, the session and a handle on the mailbox
    /// behind for the life of the runtime.
    ///
    /// Dropping the closer ends the stream, which is what lets the rest go. Any
    /// call still waiting fails, as a call on a closed lane does.
    pub fn closer(&self) -> Closer<P> {
        Closer {
            reply: self.reply.clone(),
        }
    }
}

/// Closes a [`Session`] when dropped. See [`Session::closer`].
pub struct Closer<P: Protocol> {
    reply: mpsc::UnboundedSender<Result<Frame<P::Response>>>,
}

impl<P: Protocol> Drop for Closer<P> {
    fn drop(&mut self) {
        // An error on the stream is how a transport says its lane is over.
        let _ = self
            .reply
            .send(Err(super::refusal::refuse_no("the session was closed")));
    }
}

impl<P: Protocol> Sink<Frame<P::Request>> for Session<P> {
    type Error = Error;

    /// Ready once the mailbox has a slot for the request, reserved for it. A full
    /// mailbox leaves the caller waiting here, and the drain wakes it.
    fn poll_ready(mut self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Result<()>> {
        if self.permit.is_none() {
            let permit = std::task::ready!(self.mailbox.poll_reserve(cx));
            self.permit = Some(permit);
        }
        Poll::Ready(Ok(()))
    }

    fn start_send(mut self: Pin<&mut Self>, frame: Frame<P::Request>) -> Result<()> {
        let Some(permit) = self.permit.take() else {
            return Err(Error::new("start_send without a successful poll_ready"));
        };
        let delivery = Delivery {
            from: self.from.clone(),
            frame,
            reply: self.reply.clone(),
        };
        permit.enqueue(delivery);
        self.unannounced.fetch_add(1, Ordering::SeqCst);
        Ok(())
    }

    fn poll_flush(self: Pin<&mut Self>, _: &mut task::Context<'_>) -> Poll<Result<()>> {
        while self.unannounced.load(Ordering::SeqCst) > 0 {
            let had = self.mailbox.set_state();
            self.mailbox.schedule(had);
            self.unannounced.fetch_sub(1, Ordering::SeqCst);
        }
        Poll::Ready(Ok(()))
    }

    fn poll_close(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Result<()>> {
        self.poll_flush(cx)
    }
}

impl<P: Protocol> Stream for Session<P> {
    type Item = Result<Frame<P::Response>>;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Option<Self::Item>> {
        self.replies.poll_recv(cx)
    }
}

/// An error as the response to one request.
///
/// Every generated protocol's response type has a frame that carries an
/// [`Error`], decoded from [`RJETSTREAMERROR`], which is how a handler's `Err`
/// reaches its caller. This builds one without naming the protocol, by encoding
/// the error and decoding it as that frame.
///
/// It has to be a *response*, tagged for the request it answers. Putting an `Err`
/// on the reply stream instead is not an answer to one call: the multiplexer
/// reads a stream error as the lane having failed, fails every call outstanding
/// on it, and stops reading, so calls made afterwards would never be answered.
fn error_response<R: Framer>(error: Error) -> R {
    let mut bytes = Vec::new();
    error
        .encode(&mut bytes)
        .expect("an error encodes into memory");
    R::decode(&mut bytes.as_slice(), RJETSTREAMERROR)
        .expect("a protocol's response type has an error frame")
}

/// The reply to a request the actor is handling.
///
/// Dropped without having been answered — the drain was aborted while the handler
/// was pending, or the handler panicked — it answers that one request with an
/// error. Without that the request is gone from the queue and from the round, the
/// caller's [`Session`] still holds the reply channel's other end, and the call
/// would stay pending for good, even after a new drain started and served
/// everything after it.
struct Unanswered<R: Framer> {
    tag: u16,
    reply: Option<mpsc::UnboundedSender<Result<Frame<R>>>>,
}

impl<R: Framer> Unanswered<R> {
    /// Answer the request. The sender may have gone; its answer has nowhere to go.
    fn answer(mut self, answer: Frame<R>) {
        if let Some(reply) = self.reply.take() {
            let _ = reply.send(Ok(answer));
        }
    }
}

impl<R: Framer> Drop for Unanswered<R> {
    fn drop(&mut self) {
        if let Some(reply) = self.reply.take() {
            let msg = error_response(super::refusal::refuse_no(
                "the actor stopped before it answered",
            ));
            let _ = reply.send(Ok(Frame { tag: self.tag, msg }));
        }
    }
}

/// Run the actor: take rounds from the mailbox for as long as it is held, and
/// hand each request to `service` in the order it was queued, one at a time.
///
/// That is the guarantee an actor gives: `service` sees one request at a time, in
/// each sender's order. A request that fails at the transport level is answered
/// with the error, to the sender that sent it, and the actor goes on.
///
/// `C` is the protocol the callers' channel speaks and `S` the one the service
/// speaks: a generated `XChannel` and `XService<Impl>` are different types over
/// the same requests and responses, and that is all they need to share.
pub async fn serve<C, S>(mailbox: Mailbox<Delivery<C>>, service: &mut S)
where
    C: Protocol,
    S: Server<Request = C::Request, Response = C::Response>,
{
    loop {
        // The round is held for the whole loop: the drain is running until it
        // is dropped, at the end of the `for`.
        for Delivery { from, frame, reply } in mailbox.round().await {
            // From here to the answer the request is in neither the queue nor the
            // round: if this task is aborted, or the handler panics, `Unanswered`
            // is what tells the caller.
            let tag = frame.tag;
            let pending = Unanswered {
                tag,
                reply: Some(reply),
            };
            // A request the service could not handle at all is answered with an
            // error frame for its tag, like one it declined: the stream stays
            // up for every other call.
            let answer = match service.rpc(from, frame).await {
                Ok(answer) => answer,
                Err(e) => Frame {
                    tag,
                    msg: error_response(e.into_error()),
                },
            };
            pending.answer(answer);
        }
    }
}
