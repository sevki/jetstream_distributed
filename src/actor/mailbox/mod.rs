//! **The mailbox**: a queue in front of the actor, a protocol that wakes
//! whatever drains it, and two proofs about that protocol — one of safety, one
//! of liveness.
//!
//! [`crate::actor`] proves that whatever its host accepts is accepted once, in
//! order, by one host. It deliberately says nothing about *whether* a message is
//! ever offered to the host: the network is a set, and the host may look at any
//! of it. A real actor has a mailbox instead, and a mailbox is a queue with a
//! lost-wakeup problem.
//!
//! * [`model`]  — the mailbox and its protocol: three flags, six steps, and the
//!                step boundaries the protocol's bug would live between.
//! * [`proofs`] — what the protocol keeps true ([`proofs::invariant`]), what that
//!                means for delivery ([`proofs::safety`]), and that a message
//!                enqueued is a message processed ([`proofs::liveness`]).
//!
//! # Safety and liveness are different claims
//!
//! **Safety**: nothing is lost or repeated, and each sender's messages come out
//! in the order they went in, numbered without gaps — which is exactly what the
//! actor's accept guard counts, so a drain that hands the queue to the actor in
//! order never presents a message ahead of its turn.
//!
//! **Liveness**: every enqueued message is eventually processed. This is not a
//! property of a *step*, it is a property of the infinite run, and it is false of
//! the bare machine: a run in which the drain is never given a turn satisfies
//! every safety property and processes nothing. The theorem is therefore stated
//! under [`proofs::liveness::mailbox_fair`], which says exactly which steps must
//! not be starved, and nothing else. Notably, **senders are not required to
//! send**: only operations already begun are owed a turn.
//!
//! The temporal logic it is stated in is [`crate::temporal`].
//!
//! # What is not claimed
//!
//! The service does not run this protocol: [`crate::actor::service::Host`] keeps
//! the sent set of [`crate::actor::model`] and the node that owns the actor
//! calls `accept`. This is the specification of the queue such a host would sit
//! behind, with its guarantees proved; connecting a drain loop to the service is
//! the step after it.

pub mod model;
pub mod proofs;
