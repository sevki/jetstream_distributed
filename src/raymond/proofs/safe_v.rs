//! Raymond's routing layer as a [`Safe`] protocol: `ray_inv`, kept by every step.
//!
//! The obligations are the theorems already proved in [`super::routing_layer`];
//! this file only says so in the shape [`crate::compose`] asks for. The
//! configuration is the root, as in the protocol's own instance.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::compose::Safe;
use crate::id::Id;
use crate::raymond::model::*;
use crate::raymond::proofs::routing_layer::*;

verus! {

impl Safe for RaymondProtocol {
    open spec fn inv(s: Raymond) -> bool {
        ray_inv(s)
    }

    proof fn init_establishes_inv(cfg: Id, s: Raymond) {
        theorem_ray_init_inv(s, cfg);
    }

    proof fn step_preserves_inv(pre: Raymond, post: Raymond, label: RayStep) {
        lemma_ray_step_preserves_inv(pre, post, label);
    }
}

} // verus!
