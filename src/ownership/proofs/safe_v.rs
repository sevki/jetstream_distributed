//! Ownership as a [`Safe`] protocol: its invariant, kept by every step.
//!
//! The two obligations are the theorems already proved in [`super::invariant`];
//! this file only says so in the shape [`crate::compose`] asks for, so that
//! ownership can be one part of a composition without that composition restating
//! it.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::compose::Safe;
use crate::ownership::model::*;
use crate::ownership::proofs::invariant::*;
use crate::ownership::spec::*;

verus! {

impl Safe for OwnershipProtocol {
    open spec fn inv(s: OwnershipSystem) -> bool {
        inv(s)
    }

    proof fn init_establishes_inv(cfg: (), s: OwnershipSystem) {
        lemma_init_inv(s);
    }

    proof fn step_preserves_inv(pre: OwnershipSystem, post: OwnershipSystem, label: Step) {
        lemma_step_preserves_inv(pre, post, label);
    }
}

} // verus!
