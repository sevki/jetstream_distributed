//! The actor's theorems. Every claim in the book's Reference (`book/src/reference/`) about this protocol
//! corresponds to one of the `theorem_*` items here.

#[path = "delivery_v.rs"]
pub mod delivery;
#[path = "exclusive_v.rs"]
pub mod exclusive;
#[path = "invariant_v.rs"]
pub mod invariant;
#[path = "journal_v.rs"]
pub mod journal;
#[path = "refinement_v.rs"]
pub mod refinement;
#[path = "scenario_v.rs"]
pub mod scenario;
#[path = "state_v.rs"]
pub mod state;
