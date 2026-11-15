//! What the abstract algorithm keeps true.
//!
//! * [`agreement`] — no two replicas decide differently, a decision is some
//!   replica's input, and once anyone has decided every live replica prefers the
//!   decided value. Each a consequence of `tcast`'s two guarantees.

#[path = "agreement_v.rs"]
pub mod agreement;
#[path = "isr_v.rs"]
pub mod isr;
#[path = "scenario_v.rs"]
pub mod scenario;
