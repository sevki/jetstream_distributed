//! The coupling's steps as data.
//!
//! The coordinator's four own steps (the ones that read both layers) used to be
//! written as closures run under two locks. A closure cannot be sent anywhere: it
//! cannot be proposed to a log, replayed, or applied on another machine. A
//! [`Command`] can. [`apply`] is the transition function, a dispatch to the
//! verified steps in [`crate::composed::exec`], and [`Coordinator`](super::Coordinator)
//! runs every coupling step through it.
//!
//! # What this is
//!
//! A change of shape and nothing else. The coordinator behaves as it did; the same
//! tests pass unchanged. The commands are the model's step labels with the acting
//! node written in (the transport resolved who it was; see below):
//!
//! | `Command` | model step | verified function |
//! | --- | --- | --- |
//! | `Seize { to }` | `SeizeToken` | `exec::seize_token` |
//! | `Pass { me }` | `PassToken` | `exec::pass_token` |
//! | `Acquire { node, epoch }` | `AcquireUnderToken` | `exec::acquire_under_token` |
//! | `Reconcile { node }` | `Reconcile` | `exec::reconcile` |
//!
//! # What this is not
//!
//! * **Replication.** Nothing here is replicated, and the coordinator does not
//!   survive the loss of its process. This is the first thing a replicated
//!   implementation would need, not the thing.
//! * **A trait.** There is one way to hold the state (a lock each), so there is no
//!   trait for "something that applies commands". By the rule in
//!   [#77](https://github.com/sevki/jetstream_distributed/issues/77) it is extracted
//!   when a second implementation exists, and its shape should come from what that
//!   one needs. The Reference's services page (the composed coordinator) lists what a second
//!   implementation would need.
//! * **All the steps.** The single-layer calls the coordinator carries (`write`,
//!   `begin_transfer`, `release`, the routing calls) are still methods on
//!   [`Registry`](crate::ownership::service::Registry) and
//!   [`Router`](crate::raymond::service::Router), each with its own log and, for the
//!   registry, its epoch floor. A replicated registry needs those as commands too.
//! * **Proved.** [`apply`] is plain Rust. Each arm is one verified function and
//!   [`apply`] adds only the choice of arm; that the arm matches the command is
//!   read, not checked by Verus.
//!
//! # Identity
//!
//! Every command names the acting node (`me`, `node`), as an argument. The
//! coordinator takes it from the connection ([`Context::remote`] against its roster)
//! before it builds the command, and `apply` believes it. A command that arrives
//! from anywhere else (a log, a peer) carries an identity somebody else vouched for,
//! which is [#66](https://github.com/sevki/jetstream_distributed/issues/66)'s question.

use crate::composed::exec::{
    acquire_under_token, pass_token, reconcile, seize_token, ComposedError,
};
use crate::id::{Id, IdSet};
use crate::ownership::registry::RegistryCore;
use crate::raymond::exec::RayTable;

/// One of the coupling's steps, with everything it needs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Command {
    /// `SeizeToken`: re-establish the privilege at `to`, without its holder acting.
    Seize { to: Id },
    /// `PassToken`: `me` passes the privilege to the head of its queue.
    Pass { me: Id },
    /// `AcquireUnderToken`: `node` takes the offered grant of `epoch`.
    Acquire { node: Id, epoch: u64 },
    /// `Reconcile`: `node` learns the privilege was taken from it.
    Reconcile { node: Id },
}

/// What a command did, when it did anything.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reply {
    /// The privilege was taken from `from`.
    Seized { from: Id },
    /// The privilege went to `head`.
    Passed { head: Id },
    /// The grant was taken.
    Acquired,
    /// The node reconciled.
    Reconciled,
}

/// The transition function: run `command` on the two layers' records and the set of
/// nodes that owe a reconciliation.
///
/// Each arm is the verified step of the same name; a refused command changes
/// nothing (their contracts say so).
pub fn apply(
    own: &mut RegistryCore,
    ray: &mut RayTable,
    seized: &mut IdSet,
    command: Command,
) -> Result<Reply, ComposedError> {
    match command {
        Command::Seize { to } => seize_token(own, ray, seized, to).map(|from| Reply::Seized { from }),
        Command::Pass { me } => pass_token(own, ray, seized, me).map(|head| Reply::Passed { head }),
        Command::Acquire { node, epoch } => {
            acquire_under_token(own, ray, node, epoch).map(|()| Reply::Acquired)
        }
        Command::Reconcile { node } => reconcile(ray, seized, node).map(|()| Reply::Reconciled),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const A: Id = Id(0);
    const B: Id = Id(1);

    /// `A` holds the privilege, `B` points at it, and the actor is offered to `A`.
    fn layers() -> (RegistryCore, RayTable, IdSet) {
        let own = RegistryCore::new(1, A);
        let mut ray = RayTable::new(A);
        assert!(ray.add_node(B, A));
        (own, ray, IdSet::new())
    }

    /// Commands run without a service, a lock or a roster: that is what makes them
    /// data. The actor is `Unowned`, so the privilege may be seized.
    #[test]
    fn a_seizure_is_a_command_on_the_records() {
        let (mut own, mut ray, mut seized) = layers();
        let reply = apply(&mut own, &mut ray, &mut seized, Command::Seize { to: B });
        assert!(matches!(reply, Ok(Reply::Seized { from }) if from == A));
        assert_eq!(ray.privilege, B);
        assert!(seized.contains(A), "the old holder owes a reconciliation");
        assert!(!seized.contains(B));
    }

    /// A refused command changes nothing, and says it was the coupling.
    #[test]
    fn a_refused_command_changes_nothing() {
        let (mut own, mut ray, mut seized) = layers();
        // `B` does not hold the privilege, so it may not take authority.
        let reply = apply(&mut own, &mut ray, &mut seized, Command::Acquire { node: B, epoch: 1 });
        assert!(matches!(reply, Err(ComposedError::Coupled(_))));
        assert_eq!(ray.privilege, A);
        // `A` owes nothing, so it has nothing to reconcile.
        let reply = apply(&mut own, &mut ray, &mut seized, Command::Reconcile { node: A });
        assert!(matches!(reply, Err(ComposedError::Coupled(_))));
        assert!(!seized.contains(A));
    }
}
