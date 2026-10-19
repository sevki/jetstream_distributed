//! The merge algebra, and what it buys once lifted to a run.
//!
//! * [`merge`] — `merge` is idempotent, absorbs a repeated message, never
//!   regresses, and is commutative and associative. Pure facts about two or
//!   three records; no `Cluster` in sight.
//! * [`monotone`] — the same facts, lifted through [`crate::swim::model::tr_gossip`]
//!   to a single step and then, by induction, to a whole run: **no node's
//!   record about any peer ever moves backward.** That is SWIM's convergence
//!   argument reduced to what it actually needs — not that gossip arrives in
//!   order, or even that it arrives at all, only that whatever arrives never
//!   makes a view of the world *less* accurate than it already was.
//! * [`refinement`] — the executable steps in [`crate::swim::steps`] agree with
//!   the model's `tr_gossip`, and a refutation is a gossip step rather than a
//!   new kind of step.
//! * [`table`] — the node's table ([`crate::swim::exec::SwimTable`]) learns by
//!   `tr_gossip`, hearing an accusation about oneself is two such steps, and a
//!   table always stands for a reachable cluster.

#[path = "merge_v.rs"]
pub mod merge;
#[path = "monotone_v.rs"]
pub mod monotone;
#[path = "refinement_v.rs"]
pub mod refinement;
#[path = "table_v.rs"]
pub mod table;
