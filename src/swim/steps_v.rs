//! SWIM's merge rule, executable and verified.
//!
//! The same shape as [`crate::raft::steps`] and [`crate::ownership::steps`]: the
//! decision a node makes about one peer's record is a small `u64` function with
//! a postcondition stated in terms of [`crate::swim::model`], and
//! [`crate::swim::proofs::refinement`] ties those postconditions to the model's
//! transition.
//!
//! # What a step sees
//!
//! One peer's record as this node holds it, and one record that just arrived.
//! No clock, no roster, no I/O. Which peers exist and who is allowed to speak
//! is the service's business; *what a node believes after hearing something* is
//! this file's.
//!
//! # The one place `u64` is not `nat`
//!
//! The model counts incarnations in `nat`. Only a node refuting a suspicion of
//! itself ever raises one, and it raises it to one above the accusation, so the
//! step that can run out is [`refute_step`]: an accusation at `u64::MAX` cannot
//! be out-ranked by an incarnation that fits, and wrapping would take the
//! node's record *backwards* — exactly what [`crate::swim::proofs::monotone`]
//! says never happens. So it refuses. [`merge_step`] itself never can: it only
//! ever returns one of its two arguments.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::swim::model::*;

verus! {

/// Why a step did not fire.
#[derive(Clone, Copy)]
pub enum SwimRefusal {
    /// The accusation is at the top of the `u64` incarnation space, so there is
    /// no incarnation above it to refute with. See the module docs.
    Exhausted,
}

/// A member's status, at the machine.
#[derive(Clone, Copy)]
pub enum ExecStatus {
    Alive,
    Suspect,
    Dead,
    Left,
}

/// A member's record, at `u64`.
#[derive(Clone, Copy)]
pub struct ExecRecord {
    pub incarnation: u64,
    pub status: ExecStatus,
}

impl ExecStatus {
    /// The ghost status this stands for.
    pub open spec fn view(self) -> Status {
        match self {
            ExecStatus::Alive => Status::Alive,
            ExecStatus::Suspect => Status::Suspect,
            ExecStatus::Dead => Status::Dead,
            ExecStatus::Left => Status::Left,
        }
    }
}

impl ExecRecord {
    /// The ghost record this stands for.
    pub open spec fn view(self) -> MemberRecord {
        MemberRecord { incarnation: self.incarnation as nat, status: self.status.view() }
    }
}

/// A freshly-joined, never-yet-gossiped-about peer, at the machine.
pub fn fresh_exec_record() -> (r: ExecRecord)
    ensures
        r.view() == fresh_record(),
{
    ExecRecord { incarnation: 0, status: ExecStatus::Alive }
}

/// `status_rank`, at the machine.
pub fn rank_exec(s: ExecStatus) -> (r: u8)
    ensures
        r as nat == status_rank(s.view()),
{
    match s {
        ExecStatus::Alive => 0,
        ExecStatus::Suspect => 1,
        ExecStatus::Dead => 2,
        ExecStatus::Left => 3,
    }
}

/// `key_geq`, at the machine.
pub fn key_geq_exec(a: ExecRecord, b: ExecRecord) -> (r: bool)
    ensures
        r == key_geq(a.view(), b.view()),
{
    a.incarnation > b.incarnation || (a.incarnation == b.incarnation && rank_exec(a.status)
        >= rank_exec(b.status))
}

/// **`merge`, at the machine.** Keep whichever record has the larger key,
/// `incoming` breaking a tie.
///
/// There is no refusal case and no overflow: it returns one of its arguments.
/// That is why every theorem in [`crate::swim::proofs::merge`] carries over to
/// the executable rule for free — this is the same function.
pub fn merge_step(local: ExecRecord, incoming: ExecRecord) -> (r: ExecRecord)
    ensures
        r.view() == merge(local.view(), incoming.view()),
{
    if key_geq_exec(incoming, local) {
        incoming
    } else {
        local
    }
}

/// **A node refutes an accusation about itself.**
///
/// `accused` is the incarnation the accusation (a `Suspect` or `Dead` report
/// about this node) carried. The refutation is an `Alive` record one
/// incarnation higher, which by [`crate::swim::model::key_geq`] out-ranks the
/// accusation at *any* status — a higher incarnation always wins — so merging
/// it everywhere replaces the accusation everywhere.
///
/// It is the only step that makes up a record rather than choosing between two,
/// and it can only be taken by the node it is about: nobody else may raise this
/// node's incarnation, which is what makes an incarnation a statement *by* the
/// node and not about it. The service enforces who calls it.
pub fn refute_step(accused: u64) -> (r: Result<ExecRecord, SwimRefusal>)
    ensures
        match r {
            Ok(rec) => {
                &&& rec.view() == (MemberRecord {
                    incarnation: accused as nat + 1,
                    status: Status::Alive,
                })
                &&& rec.incarnation > accused
            },
            Err(_) => accused == u64::MAX,
        },
{
    if accused == u64::MAX {
        Err(SwimRefusal::Exhausted)
    } else {
        Ok(ExecRecord { incarnation: accused + 1, status: ExecStatus::Alive })
    }
}

} // verus!
