//! The executable routing steps agree with the model.
//!
//! The obligations [`crate::raft::proofs::refinement`] discharges for the Raft
//! steps: when a step fires, the model's transition fires, to exactly the state
//! the step computed; and when it refuses, the model's transition is not
//! enabled. The second half carries the weight, because a step that refused
//! everything would satisfy the first perfectly.
//!
//! # The couplings
//!
//! A step sees one node's scalars; the model's state is a whole [`Raymond`]. The
//! correspondence is named as hypotheses rather than assumed:
//!
//! | Hypothesis | What supplies it |
//! | --- | --- |
//! | `holder == r.holder[n]`, `asked == r.asked[n]`, `using == r.using[n]` | the router's own table, read under its lock |
//! | `queue_len == r.queue[n].len()`, `queue_head == r.queue[n][0]` | the same table's queue |
//! | `privilege == r.privilege` | the router's record of where the privilege is |
//! | `sent == r.requests.contains((from, at))` | the router's record of what has been sent |
//! | `head_is_node == r.nodes.contains(head)` | the router's roster |
//!
//! None of them is exotic, and each is something the service keeps true by
//! holding the whole table under one lock. That the *table* is a faithful
//! `Raymond` is the service's claim and is tested, not proved.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

use crate::ownership::model::*;
use crate::raymond::model::*;
use crate::raymond::steps::*;

verus! {

/// Where `RequestCs` sends the routing state.
pub open spec fn request_cs_post(r: Raymond, n: Id) -> Raymond {
    Raymond {
        nodes: r.nodes,
        holder: r.holder,
        queue: r.queue.insert(n, r.queue[n].push(n)),
        asked: r.asked,
        using: r.using,
        requests: r.requests,
        privilege: r.privilege,
    }
}

/// Where `MakeRequest` sends it.
pub open spec fn make_request_post(r: Raymond, n: Id) -> Raymond {
    Raymond {
        nodes: r.nodes,
        holder: r.holder,
        queue: r.queue,
        asked: r.asked.insert(n, true),
        using: r.using,
        requests: r.requests.insert((n, r.holder[n])),
        privilege: r.privilege,
    }
}

/// Where `ReceiveRequest` sends it.
pub open spec fn receive_request_post(r: Raymond, at: Id, from: Id) -> Raymond {
    Raymond {
        nodes: r.nodes,
        holder: r.holder,
        queue: r.queue.insert(at, r.queue[at].push(from)),
        asked: r.asked,
        using: r.using,
        requests: r.requests,
        privilege: r.privilege,
    }
}

/// Where `AssignPrivilege` sends it.
pub open spec fn assign_post(r: Raymond, n: Id, head: Id) -> Raymond {
    Raymond {
        nodes: r.nodes,
        holder: r.holder.insert(n, head).insert(head, head),
        queue: r.queue.insert(n, r.queue[n].drop_first()),
        asked: r.asked.insert(n, false),
        using: r.using,
        requests: r.requests,
        privilege: head,
    }
}

/// Where `EnterCs` sends it.
pub open spec fn enter_cs_post(r: Raymond, n: Id) -> Raymond {
    Raymond {
        nodes: r.nodes,
        holder: r.holder,
        queue: r.queue.insert(n, r.queue[n].drop_first()),
        asked: r.asked,
        using: r.using.insert(n, true),
        requests: r.requests,
        privilege: r.privilege,
    }
}

/// Where `ExitCs` sends it.
pub open spec fn exit_cs_post(r: Raymond, n: Id) -> Raymond {
    Raymond {
        nodes: r.nodes,
        holder: r.holder,
        queue: r.queue,
        asked: r.asked,
        using: r.using.insert(n, false),
        requests: r.requests,
        privilege: r.privilege,
    }
}

/// `RequestCs` has no scalar guard — a node may always ask — so its step is the
/// queue push and there is nothing to refuse. The theorem is that the post-state
/// above is the model's.
pub proof fn theorem_request_cs_post_is_the_model_step(r: Raymond, n: Id)
    requires
        r.nodes.contains(n),
    ensures
        ray_request_cs(r, request_cs_post(r, n), n),
{
}

/// When the make request step fires, the model's transition fires, to exactly the state computed.
pub proof fn theorem_make_request_step_refines(r: Raymond, n: Id)
    requires
        ray_maps_total(r),
        r.nodes.contains(n),
        make_request_fires(n, r.holder[n], r.queue[n].len(), r.asked[n]),
    ensures
        ray_make_request(r, make_request_post(r, n), n),
{
}

/// A refused `MakeRequest` is a transition the model could not have taken
/// either, whatever state it was sent to.
pub proof fn theorem_make_request_step_refuses_exactly_when_disabled(
    r: Raymond,
    post: Raymond,
    n: Id,
)
    requires
        ray_maps_total(r),
        r.nodes.contains(n),
        !make_request_fires(n, r.holder[n], r.queue[n].len(), r.asked[n]),
    ensures
        !ray_make_request(r, post, n),
{
}

/// When the receive request step fires, the model's transition fires, to exactly the state computed.
pub proof fn theorem_receive_request_step_refines(r: Raymond, at: Id, from: Id)
    requires
        r.nodes.contains(at),
        r.nodes.contains(from),
        receive_request_fires(r.requests.contains((from, at))),
    ensures
        ray_receive_request(r, receive_request_post(r, at, from), at, from),
{
}

/// A refused receive request step is a transition the model could not have taken either, whatever state it was sent to.
pub proof fn theorem_receive_request_step_refuses_exactly_when_disabled(
    r: Raymond,
    post: Raymond,
    at: Id,
    from: Id,
)
    requires
        r.nodes.contains(at),
        r.nodes.contains(from),
        !receive_request_fires(r.requests.contains((from, at))),
    ensures
        !ray_receive_request(r, post, at, from),
{
}

/// When the assign step fires, the model's transition fires, to exactly the state computed.
pub proof fn theorem_assign_step_refines(r: Raymond, n: Id, head: Id)
    requires
        ray_maps_total(r),
        r.nodes.contains(n),
        r.queue[n].len() > 0,
        r.queue[n][0] == head,
        assign_fires(
            n,
            r.privilege,
            r.holder[n],
            r.using[n],
            r.queue[n].len(),
            head,
            r.nodes.contains(head),
        ),
    ensures
        ray_assign_privilege(r, assign_post(r, n, head), n, head),
{
}

/// A refused assign step is a transition the model could not have taken either, whatever state it was sent to.
pub proof fn theorem_assign_step_refuses_exactly_when_disabled(
    r: Raymond,
    post: Raymond,
    n: Id,
    head: Id,
)
    requires
        ray_maps_total(r),
        r.nodes.contains(n),
        r.queue[n].len() > 0,
        r.queue[n][0] == head,
        !assign_fires(
            n,
            r.privilege,
            r.holder[n],
            r.using[n],
            r.queue[n].len(),
            head,
            r.nodes.contains(head),
        ),
    ensures
        !ray_assign_privilege(r, post, n, head),
{
}

/// With an empty queue there is no `head` to name, so the step refuses and no
/// `head` makes the model's transition enabled.
pub proof fn theorem_assign_step_refuses_an_empty_queue(
    r: Raymond,
    post: Raymond,
    n: Id,
    head: Id,
)
    requires
        ray_maps_total(r),
        r.nodes.contains(n),
        r.queue[n].len() == 0,
    ensures
        !ray_assign_privilege(r, post, n, head),
{
}

/// When the enter cs step fires, the model's transition fires, to exactly the state computed.
pub proof fn theorem_enter_cs_step_refines(r: Raymond, n: Id)
    requires
        ray_maps_total(r),
        r.nodes.contains(n),
        r.queue[n].len() > 0,
        enter_cs_fires(n, r.holder[n], r.using[n], r.queue[n].len(), r.queue[n][0]),
    ensures
        ray_enter_cs(r, enter_cs_post(r, n), n),
{
}

/// A refused enter cs step is a transition the model could not have taken either, whatever state it was sent to.
pub proof fn theorem_enter_cs_step_refuses_exactly_when_disabled(
    r: Raymond,
    post: Raymond,
    n: Id,
)
    requires
        ray_maps_total(r),
        r.nodes.contains(n),
        r.queue[n].len() > 0,
        !enter_cs_fires(n, r.holder[n], r.using[n], r.queue[n].len(), r.queue[n][0]),
    ensures
        !ray_enter_cs(r, post, n),
{
}

/// With an empty queue there is nothing at the head, so the model's enter cs transition is not enabled either.
pub proof fn theorem_enter_cs_step_refuses_an_empty_queue(r: Raymond, post: Raymond, n: Id)
    requires
        ray_maps_total(r),
        r.nodes.contains(n),
        r.queue[n].len() == 0,
    ensures
        !ray_enter_cs(r, post, n),
{
}

/// When the exit cs step fires, the model's transition fires, to exactly the state computed.
pub proof fn theorem_exit_cs_step_refines(r: Raymond, n: Id)
    requires
        ray_maps_total(r),
        r.nodes.contains(n),
        exit_cs_fires(r.using[n]),
    ensures
        ray_exit_cs(r, exit_cs_post(r, n), n),
{
}

/// A refused exit cs step is a transition the model could not have taken either, whatever state it was sent to.
pub proof fn theorem_exit_cs_step_refuses_exactly_when_disabled(
    r: Raymond,
    post: Raymond,
    n: Id,
)
    requires
        ray_maps_total(r),
        r.nodes.contains(n),
        !exit_cs_fires(r.using[n]),
    ensures
        !ray_exit_cs(r, post, n),
{
}

} // verus!
