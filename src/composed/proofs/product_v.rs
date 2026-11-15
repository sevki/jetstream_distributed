//! **The composed machine is the product of ownership and Raymond.**
//!
//! [`crate::composed::model`] writes the composition by hand: one state, one step
//! type, a guard per variant. [`crate::compose`] writes composition in general: a
//! [`Product`] of two protocols under a [`Coupling`]. This file proves that the
//! first is an instance of the second, so the hand-written model is not a
//! special case that the general one fails to cover, and the general theorem
//! ([`crate::compose_safety`]) applies to it.
//!
//! Nothing in the composed model changes. Its theorems stay stated against
//! `composed_step`; what this adds is the bridge.
//!
//! The bridge is exact, in both directions, and for each kind of step:
//!
//! * `Own` and `AcquireUnderToken` are the product's `Left` (ownership moves
//!   alone); the second is the one `Acquire` of *this* actor, guarded by the
//!   token;
//! * `Ray` and `PassToken` are the product's `Right`; the second is Raymond's
//!   `AssignPrivilege`, the one step that moves the token;
//! * `SeizeToken` and `Reconcile` are the product's `Joint`: the coordinator's,
//!   which edit Raymond's state without being a Raymond step.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::compose::*;
use crate::composed::model::*;
use crate::composed::proofs::coupling::*;
use crate::id::Id;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::proofs::safe::*;
use crate::ownership::spec::*;
use crate::protocol::Protocol;
use crate::raymond::model::*;
use crate::raymond::proofs::safe::*;

verus! {

/// The composed machine, as the product of ownership and Raymond.
pub type OwnRay = Product<OwnershipProtocol, RaymondProtocol, OwnRayCoupling>;

/// A composed state, read as a state of the product.
pub open spec fn to_prod(c: Composed) -> Prod<OwnershipSystem, Raymond, ComposedGlue> {
    Prod { a: c.own, b: c.ray, g: ComposedGlue { actor: c.actor, seized: c.seized } }
}

/// A state of the product, read as a composed state.
pub open spec fn from_prod(p: Prod<OwnershipSystem, Raymond, ComposedGlue>) -> Composed {
    Composed { own: p.a, ray: p.b, actor: p.g.actor, seized: p.g.seized }
}

/// The product step that a composed step is. Depends on the pre-state, because
/// whether an `Acquire` is `AcquireUnderToken` depends on which actor is governed.
pub open spec fn label_of(c: Composed, s: ComposedStep) -> ProdStep<Step, RayStep, CoordinatorStep> {
    match s {
        ComposedStep::Ray { ray_step } => ProdStep::Right { lb: ray_step },
        ComposedStep::Own { own_step } => ProdStep::Left { la: own_step },
        ComposedStep::PassToken { node, head } => ProdStep::Right {
            lb: RayStep::AssignPrivilege { node, head },
        },
        ComposedStep::SeizeToken { from, to } => ProdStep::Joint {
            lc: CoordinatorStep::Seize { from, to },
        },
        ComposedStep::Reconcile { node } => ProdStep::Joint {
            lc: CoordinatorStep::Reconcile { node },
        },
        ComposedStep::AcquireUnderToken { node } => ProdStep::Left {
            la: Step::Acquire { actor: c.actor, node },
        },
    }
}

/// The composed step that a product step is.
pub open spec fn step_of(c: Composed, l: ProdStep<Step, RayStep, CoordinatorStep>) -> ComposedStep {
    match l {
        ProdStep::Left { la } => match la {
            Step::Acquire { actor, node } => if actor == c.actor {
                ComposedStep::AcquireUnderToken { node }
            } else {
                ComposedStep::Own { own_step: la }
            },
            _ => ComposedStep::Own { own_step: la },
        },
        ProdStep::Right { lb } => match lb {
            RayStep::AssignPrivilege { node, head } => ComposedStep::PassToken { node, head },
            _ => ComposedStep::Ray { ray_step: lb },
        },
        ProdStep::Joint { lc } => match lc {
            CoordinatorStep::Seize { from, to } => ComposedStep::SeizeToken { from, to },
            CoordinatorStep::Reconcile { node } => ComposedStep::Reconcile { node },
        },
    }
}

/// A composed step is the product step it is labelled as.
pub proof fn lemma_composed_step_is_a_product_step(c: Composed, d: Composed, s: ComposedStep)
    requires
        composed_step(c, d, s),
    ensures
        OwnRay::step(to_prod(c), to_prod(d), label_of(c, s)),
{
}

/// A product step is the composed step it is read as.
pub proof fn lemma_product_step_is_a_composed_step(
    c: Composed,
    d: Composed,
    l: ProdStep<Step, RayStep, CoordinatorStep>,
)
    requires
        OwnRay::step(to_prod(c), to_prod(d), l),
    ensures
        composed_step(c, d, step_of(c, l)),
{
}

/// **The composed machine's transition relation is the product's.**
pub proof fn theorem_composed_next_is_the_product_next(c: Composed, d: Composed)
    ensures
        composed_next(c, d) <==> OwnRay::next(to_prod(c), to_prod(d)),
{
    if composed_next(c, d) {
        let s = choose|s: ComposedStep| composed_step(c, d, s);
        lemma_composed_step_is_a_product_step(c, d, s);
        assert(OwnRay::step(to_prod(c), to_prod(d), label_of(c, s)));
    }
    if OwnRay::next(to_prod(c), to_prod(d)) {
        let l = choose|l: ProdStep<Step, RayStep, CoordinatorStep>|
            OwnRay::step(to_prod(c), to_prod(d), l);
        lemma_product_step_is_a_composed_step(c, d, l);
        assert(composed_step(c, d, step_of(c, l)));
    }
}

/// **The composed machine's initial states are the product's**, at some root.
pub proof fn theorem_composed_init_is_the_product_init(c: Composed)
    ensures
        composed_init(c) <==> exists|root: Id| OwnRay::init(((), root), to_prod(c)),
{
    if composed_init(c) {
        let root = choose|root: Id| ray_init(c.ray, root);
        assert(OwnRay::init(((), root), to_prod(c)));
    }
    if exists|root: Id| OwnRay::init(((), root), to_prod(c)) {
        let root = choose|root: Id| OwnRay::init(((), root), to_prod(c));
        assert(ray_init(c.ray, root));
    }
}

/// The coupling's invariant: what `composed_inv` says beyond each layer's own.
impl SafeCoupling<OwnershipProtocol, RaymondProtocol> for OwnRayCoupling {
    open spec fn coupled(s: Prod<OwnershipSystem, Raymond, ComposedGlue>) -> bool {
        &&& s.a.actors.contains_key(s.g.actor)
        &&& couples(s.b, s.a.actors[s.g.actor])
        &&& s.b.nodes == s.a.nodes
        &&& (forall|n: Id| #[trigger] is_stale_holder(s.b, n) ==> s.g.seized.contains(n))
    }

    proof fn coupled_at_init(cfg: ((), Id), s: Prod<OwnershipSystem, Raymond, ComposedGlue>) {
        let c = from_prod(s);
        assert(to_prod(c) == s);
        assert(composed_init(c));
        lemma_composed_init_inv(c);
    }

    proof fn coupled_after(
        pre: Prod<OwnershipSystem, Raymond, ComposedGlue>,
        post: Prod<OwnershipSystem, Raymond, ComposedGlue>,
        label: ProdStep<Step, RayStep, CoordinatorStep>,
    ) {
        let c = from_prod(pre);
        let d = from_prod(post);
        assert(to_prod(c) == pre);
        assert(to_prod(d) == post);
        assert(composed_inv(c));
        lemma_product_step_is_a_composed_step(c, d, label);
        theorem_composed_step_preserves_inv(c, d, step_of(c, label));
    }
}

} // verus!
