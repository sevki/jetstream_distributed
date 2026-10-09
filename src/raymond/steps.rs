//! Raymond's routing decisions, executable and verified.
//!
//! The same shape as [`crate::raft::steps`] and [`crate::ownership::steps`]: each
//! decision a node makes about its own routing entries is a small `u64`
//! function whose postcondition is stated in terms of [`crate::raymond::model`],
//! and [`crate::raymond::proofs::refinement`] ties those postconditions to the
//! model's transitions.
//!
//! # What a step sees
//!
//! **One node's scalars**: where its holder pointer points, whether it has an
//! outstanding request, whether it is inside its critical section, how long its
//! queue is and what is at the head of it. It sees no queue, no request set and
//! no other node. Keeping the queue itself out is deliberate — a `Vec` and a
//! `Seq` correspond only through a proof about the container, and none of these
//! decisions needs more than the length and the first element, which the caller
//! hands over.
//!
//! That is the narrowing to be honest about. The model's guards quantify over
//! `Seq<NodeId>`; these read `queue_len` and `queue_head`, and
//! [`crate::raymond::proofs::refinement`] states the correspondence as a
//! hypothesis (`queue_head == r.queue[n][0]`) rather than assuming it.
//!
//! # Two things the service supplies
//!
//! * **That a node exists.** Every model transition begins with
//!   `pre.nodes.contains(..)`. A step cannot know the membership, so the service
//!   checks it before calling one, and `head_is_node` carries the same fact for
//!   the node being handed the privilege.
//! * **That a request was sent.** [`receive_request_fires`] is the model's
//!   `requests.contains((from, at))`, supplied as a boolean from the router's own
//!   record of what has been sent.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::ownership::model::NodeId;

verus! {

/// Why a step did not fire. The protocol's reasons only.
#[derive(Clone, Copy)]
pub enum RayRefusal {
    /// This node holds the privilege itself, so there is nobody to ask.
    HoldsPrivilege,
    /// Nothing is queued, so there is nothing to ask for.
    EmptyQueue,
    /// A request towards the holder is already outstanding.
    AlreadyAsked,
    /// No request from that node to this one was ever sent.
    NotSent,
    /// This node does not hold the privilege.
    NotPrivileged,
    /// This node does not believe it holds the privilege.
    NotHolder,
    /// This node is inside its critical section.
    InCriticalSection,
    /// This node is not inside its critical section.
    NotInCriticalSection,
    /// The head of the queue is this node itself: it enters, it does not pass.
    HeadIsSelf,
    /// The head of the queue is not this node itself: it passes, it does not
    /// enter.
    HeadIsNotSelf,
    /// The head of the queue is not a node.
    HeadNotANode,
}

/// `ray_make_request`'s guard: this node is not the root, has something queued,
/// and has not already asked.
pub open spec fn make_request_fires(me: nat, holder: nat, queue_len: nat, asked: bool) -> bool {
    &&& holder != me
    &&& queue_len > 0
    &&& !asked
}

/// `ray_receive_request`'s guard on the message: it was sent.
pub open spec fn receive_request_fires(sent: bool) -> bool {
    sent
}

/// `ray_assign_privilege`'s guard on the node passing the privilege on.
///
/// It reads **both** the authoritative fact (`privilege == me`) and the belief
/// (`holder == me`): the model requires `has_token` *and* `believes_holds`, and
/// a service that checked only the belief would let a stale holder pass a
/// privilege it does not have.
pub open spec fn assign_fires(
    me: nat,
    privilege: nat,
    holder: nat,
    using: bool,
    queue_len: nat,
    queue_head: nat,
    head_is_node: bool,
) -> bool {
    &&& privilege == me
    &&& holder == me
    &&& !using
    &&& queue_len > 0
    &&& queue_head != me
    &&& head_is_node
}

/// `ray_enter_cs`'s guard.
///
/// **Belief, not authority** — the model's own words: a node decides to enter on
/// what it knows, and a stale holder does not know it is stale. There is
/// deliberately no `privilege` parameter here.
pub open spec fn enter_cs_fires(
    me: nat,
    holder: nat,
    using: bool,
    queue_len: nat,
    queue_head: nat,
) -> bool {
    &&& holder == me
    &&& !using
    &&& queue_len > 0
    &&& queue_head == me
}

/// `ray_exit_cs`'s guard: the node is in its critical section.
pub open spec fn exit_cs_fires(using: bool) -> bool {
    using
}

/// Forward a request one hop towards the privilege. Returns where it goes: the
/// holder pointer, resolved *now*, which is what the model records.
pub fn make_request_step(me: u64, holder: u64, queue_len: u64, asked: bool) -> (r: Result<
    u64,
    RayRefusal,
>)
    ensures
        match r {
            Ok(dest) => make_request_fires(me as nat, holder as nat, queue_len as nat, asked)
                && dest == holder,
            Err(_) => !make_request_fires(me as nat, holder as nat, queue_len as nat, asked),
        },
{
    if holder == me {
        Err(RayRefusal::HoldsPrivilege)
    } else if queue_len == 0 {
        Err(RayRefusal::EmptyQueue)
    } else if asked {
        Err(RayRefusal::AlreadyAsked)
    } else {
        Ok(holder)
    }
}

/// Accept a request that was sent.
pub fn receive_request_step(sent: bool) -> (r: Result<(), RayRefusal>)
    ensures
        match r {
            Ok(_) => receive_request_fires(sent),
            Err(_) => !receive_request_fires(sent),
        },
{
    if sent {
        Ok(())
    } else {
        Err(RayRefusal::NotSent)
    }
}

/// Hand the privilege to the head of the queue. Returns the node it goes to.
pub fn assign_step(
    me: u64,
    privilege: u64,
    holder: u64,
    using: bool,
    queue_len: u64,
    queue_head: u64,
    head_is_node: bool,
) -> (r: Result<u64, RayRefusal>)
    ensures
        match r {
            Ok(head) => assign_fires(
                me as nat,
                privilege as nat,
                holder as nat,
                using,
                queue_len as nat,
                queue_head as nat,
                head_is_node,
            ) && head == queue_head,
            Err(_) => !assign_fires(
                me as nat,
                privilege as nat,
                holder as nat,
                using,
                queue_len as nat,
                queue_head as nat,
                head_is_node,
            ),
        },
{
    if privilege != me {
        Err(RayRefusal::NotPrivileged)
    } else if holder != me {
        Err(RayRefusal::NotHolder)
    } else if using {
        Err(RayRefusal::InCriticalSection)
    } else if queue_len == 0 {
        Err(RayRefusal::EmptyQueue)
    } else if queue_head == me {
        Err(RayRefusal::HeadIsSelf)
    } else if !head_is_node {
        Err(RayRefusal::HeadNotANode)
    } else {
        Ok(queue_head)
    }
}

/// Enter the critical section: this node believes it holds the privilege and is
/// at the head of its own queue.
pub fn enter_cs_step(me: u64, holder: u64, using: bool, queue_len: u64, queue_head: u64) -> (r:
    Result<(), RayRefusal>)
    ensures
        match r {
            Ok(_) => enter_cs_fires(me as nat, holder as nat, using, queue_len as nat, queue_head as nat),
            Err(_) => !enter_cs_fires(
                me as nat,
                holder as nat,
                using,
                queue_len as nat,
                queue_head as nat,
            ),
        },
{
    if holder != me {
        Err(RayRefusal::NotHolder)
    } else if using {
        Err(RayRefusal::InCriticalSection)
    } else if queue_len == 0 {
        Err(RayRefusal::EmptyQueue)
    } else if queue_head != me {
        Err(RayRefusal::HeadIsNotSelf)
    } else {
        Ok(())
    }
}

/// Leave the critical section.
pub fn exit_cs_step(using: bool) -> (r: Result<(), RayRefusal>)
    ensures
        match r {
            Ok(_) => exit_cs_fires(using),
            Err(_) => !exit_cs_fires(using),
        },
{
    if using {
        Ok(())
    } else {
        Err(RayRefusal::NotInCriticalSection)
    }
}

} // verus!
