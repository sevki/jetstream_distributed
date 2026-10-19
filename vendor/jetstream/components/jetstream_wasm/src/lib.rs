//! jetstream on wasm32.
//!
//! Empty for now. The host transport that used to live here moved to
//! plateau (`plateau_guest::transport`): the host end of a guest's lane is
//! the actor system, which jetstream doesn't know about.

pub extern crate js_sys;
pub extern crate wasm_bindgen;
