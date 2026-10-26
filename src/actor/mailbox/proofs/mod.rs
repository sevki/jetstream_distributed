//! The mailbox's theorems. Every claim in the book's Reference (`book/src/reference/`) about this protocol
//! corresponds to one of the `theorem_*` items here.

#[path = "invariant_v.rs"]
pub mod invariant;
#[path = "liveness_v.rs"]
pub mod liveness;
#[path = "refinement_v.rs"]
pub mod refinement;
#[path = "safety_v.rs"]
pub mod safety;
#[path = "scenario_v.rs"]
pub mod scenario;
