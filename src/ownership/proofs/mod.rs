//! The ownership theorems. Every claim in the book's Reference (`book/src/reference/`) about this protocol
//! corresponds to one of the `theorem_*` items here.

#[path = "adversarial_v.rs"]
pub mod adversarial;
#[path = "exclusivity_v.rs"]
pub mod exclusivity;
#[path = "fencing_v.rs"]
pub mod fencing;
#[path = "invariant_v.rs"]
pub mod invariant;
#[path = "properties_v.rs"]
pub mod properties;
#[path = "refinement_v.rs"]
pub mod refinement;
#[path = "registry_v.rs"]
pub mod registry;
#[path = "safe_v.rs"]
pub mod safe;
#[path = "tokens_v.rs"]
pub mod tokens;
#[path = "transfer_v.rs"]
pub mod transfer;
