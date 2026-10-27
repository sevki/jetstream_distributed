# SWIM: gossip membership, bought by merge rather than majority

Ownership and Raft both spend a majority round-trip to get one authoritative
answer. SWIM does not try to agree on anything: every node keeps its own view
of who else is alive, those views disagree constantly, and the protocol's
only promise is that disagreements resolve rather than compound. That is a
different kind of promise from Election Safety or exclusive ownership, and it
is bought a different way — by an algebraic property of a merge rule, not by
quorum intersection.

**This is the first piece, not the whole protocol**, in the same sense
`src/raft/model_t.rs` was the first piece of Raft: the state space and one
transition, proved correct on their own terms, with the probe timer,
indirect-ping fallback and dissemination piggyback still to come. The piece
chosen first is the one everything else depends on being right: `state.go`'s
merge rule, the one function every gossip message, probe timeout and
self-refutation in [hashicorp/memberlist](https://github.com/hashicorp/memberlist)
ultimately calls.

## The record, and the rule for merging two of them

A `MemberRecord` is an incarnation number and a status — `Alive`, `Suspect` or
`Dead` — and `key_geq` compares two of them: a higher incarnation always wins,
and at equal incarnations the more-dead status wins. `merge` keeps whichever
side has the larger key. That is the entire rule; `tr_gossip` is `merge`
applied to whatever a peer's own view already holds and whatever record just
arrived, and a probe timeout or a self-refutation is only a different choice
of *which* record arrived, not a different rule for applying it.

| | claim | theorem | assumes |
|---|---|---|---|
| S1 | **Merging a record with itself changes nothing** | `swim::proofs::merge::theorem_merge_is_idempotent` | none |
| S2 | **Merging in the same message twice has no more effect than merging it in once** — the fact that lets gossip's real delivery model, at-least-once and arbitrarily duplicated, survive contact with `merge` at all | `swim::proofs::merge::theorem_merge_absorbs_a_repeat` | none |
| S3 | **A record that does not out-rank the local one cannot change it** — the safety half: a stale or weaker report is accepted nowhere, at any incarnation | `swim::proofs::merge::theorem_merge_never_regresses` | none |
| S4 | **`merge` does not care which side is called local and which is called incoming** — true of what it returns even though the comparison it is built from is not symmetric, because the one case where the asymmetry could show, a tie, is a tie between two copies of the same record | `swim::proofs::merge::theorem_merge_is_commutative` | `status_rank` is injective (`swim::model::lemma_rank_is_injective`) |
| S5 | **No node's record about any peer ever moves backward, across a whole run** — S1–S4 are arithmetic about two records; this is what they add up to once lifted through every step of an execution, and it is the actual convergence argument SWIM needs: not that gossip arrives in order, or even that it arrives at all, only that whatever arrives never makes a view of the world *less* accurate than it already was | `swim::proofs::monotone::theorem_a_record_key_never_falls_across_a_run` | none beyond `key_geq`'s own transitivity (`swim::proofs::merge::lemma_key_geq_transitive`) |
| S6 | **`merge` does not care how three records are grouped** — S4 alone only says swapping two arguments doesn't matter; a node's view is built by folding in one delivered record after another, so order-independence needs grouping not to matter either, which is what associativity says | `swim::proofs::merge::theorem_merge_is_associative` | `key_geq` is total and antisymmetric up to record equality (`swim::proofs::merge::lemma_key_geq_total`, `lemma_key_geq_antisymmetric`) |
| S7 | **The executable `merge_step` is the model's `merge`, and applying it is the model's `tr_gossip`** — the service's merge is not a second implementation that the algebra above is merely about; it is the function those theorems quantify over, and a node that merges an arrival into its table and writes the result back has taken exactly the model's step | `swim::steps::merge_step` (its `ensures`), `swim::proofs::refinement::theorem_merge_step_is_a_gossip_step` | the executable record is the model's (`local.view() == record_of(pre, n)`), which the service keeps true by holding its table under one lock |
| S8 | **A refutation out-ranks the accusation it answers, and everything its author could have held when it was made** — alive at one incarnation above beats suspect *and* dead at the accusation's, because a higher incarnation wins at any status | `swim::proofs::refinement::theorem_a_refutation_outranks_what_it_answers` | `held.incarnation <= accused` |
| S9 | **A refutation is a gossip step, not a new kind of step, and `refute_step` computes it** — the model gains no transition for answering an accusation; the node applies `tr_gossip` to a record it made itself, and the executable step makes exactly that record or refuses at the top of the `u64` space | `swim::proofs::refinement::theorem_a_refutation_is_a_gossip_step`, `theorem_refute_step_is_the_refutation`, `swim::steps::refute_step` (its `ensures`) | none |

| S10 | **The node's table is the model.** `exec::SwimTable` — what a node keeps — reads the model's `record_of` (no entry is the fresh record), and `learn` writes `merge` of what is held and what arrived and changes nothing else; a table standing for a cluster that learns a record stands for the cluster `tr_gossip` leads to, and a fresh table stands for `swim_init` | `swim::proofs::table::theorem_new_table_is_the_initial_cluster`, `theorem_learn_is_a_gossip_step` | the table is well formed (each member once) |
| S11 | **Hearing an accusation about oneself is two gossip steps.** `SwimTable::hear` merges the record and, if it was the node's *own* that changed, merges the refutation on top of it; the model sees `tr_gossip` twice, and the table ends up believing the refutation. At the top of the incarnation space the second step is refused and the first has happened | `swim::proofs::table::theorem_hearing_oneself_accused_is_two_gossip_steps` | the table stands for the cluster |
| S12 | **A table never believes less than it did, and always stands for a reachable cluster.** Whatever it learns, what it then holds for any member out-ranks or equals what it held; and a reachable cluster plus a learned record is a reachable cluster, so S5 is a statement about what the table holds | `swim::proofs::table::theorem_learning_never_lowers_a_belief`, `theorem_a_table_stands_for_a_reachable_cluster_after_learning` | the table stands for a reachable cluster |
| S13 | **A departure outlasts every report at or below its incarnation.** `Left` ranks above `Dead`, so a suspicion timer that was already running, a late `Dead` verdict, or an old `Alive` cannot turn a node that announced its leaving into a failure or a recovery; merging any record at the same or an older incarnation into a `Left` record returns it unchanged. The one same-incarnation record that is itself `Left` is the same record, so repeating it changes nothing | `swim::proofs::merge::theorem_a_departure_outlasts_every_report_at_or_below_it` | none |
| S14 | **Only a higher incarnation brings a departed member back.** The converse of S13 in the form a service uses: if hearing a record changed what a node believed about a member that had left, the record carried a higher incarnation, which only that member can have produced. Nobody else can revive it | `swim::proofs::merge::theorem_only_a_higher_incarnation_revives_a_departure` | none beyond S13 |

**What S10–S14 do not cover.** The table is a verified core, and `Node` is the
shell around it: the roster and the admission policy (which numbers are members,
who may speak and who may join), the lock, the audit log, the batch limit, and the
order a batch is applied in are plain Rust that the tests exercise. The theorems
are about one record at a time. In particular nothing proves that `Node::leave`
writes the departure *without* answering it with a refutation: it does so by
calling the table's own `learn` rather than the path a received message takes, and
`tests/swim_dynamic.rs::a_node_does_not_refute_its_own_departure` is what fails if
that changes.

**Joining and leaving.** The model never assumed a fixed membership: a node absent
from the view is exactly a node at the fresh record. What was fixed was the
*service's* roster. `Node::new` still builds that closed cluster. `Node::admitting`
builds one that grows: a caller whose address is not yet known is put to an
`Admission` policy, a function from the connection's address to the member number
that address may be, and is admitted if the policy names one and there is room.
There is no join call: a join is the first `ping` or `sync` from an address the
policy lets in, the `sync` reply is the whole table, and the others hear of the
newcomer by gossip. The member number comes out of the policy and the connection,
never out of the request. `Node::leave` records the node as `Left` at its held
incarnation and returns that record for the caller to tell its peers. What this
does **not** do: nothing decides who the policy should admit (the example's admits
every loopback address; a deployment writes its own); where a member lives is the
deployment's mapping from member number to address, not something SWIM gossips;
members are never forgotten, so a departed member's record is kept (it is what
keeps S13 true) and counts against the same bound of `MAX_UPDATES` members; a member
that comes back must do so from the same address; and a node that leaves and tells
nobody is, to the cluster, a node that died.

**S4 is worth pausing on, because the asymmetry it dismisses is real.**
`key_geq(a, b)` and `key_geq(b, a)` are different expressions, and reading
`merge`'s definition — `if key_geq(incoming, local) { incoming } else {
local }` — the incoming side breaks a tie. So `merge(a, b)` and `merge(b, a)`
each hand a *different call* the tie-breaking advantage. What makes the
theorem true anyway is `status_rank`'s injectivity: a `MemberRecord` is
exactly its incarnation and its status, and if two records tie on
`key_geq` — equal incarnation, equal rank — then by injectivity they have
equal status too, so they were never two different records to begin with.
`lemma_rank_is_injective` is a case split on the four enum variants;
S4 is the only theorem in this module that spends it.

**What the proofs are not** is a claim that gossip converges *in practice*.
Convergence needs every node's view to eventually receive every update, which
is a property of the dissemination schedule — how often a node piggybacks
which records onto which probes — and that schedule is not modelled here at
all. S5 is the half of the argument that has nothing to do with scheduling:
whatever arrives, however late or however duplicated, can only move things
forward. The other half — that something eventually arrives — is exactly the
network-timing piece that is still future work.

## The service

`src/swim/service/` serves the protocol over
[Jetstream](https://github.com/sevki/jetstream) RPC: `#[service] trait
Membership` with `ping` and `sync`, implemented by a `Node` whose table is
written in exactly one place, by `exec::SwimTable::hear` — the verified table, whose
merge is `steps::merge_step` (S10–S12).

Both methods do the same thing to the receiver — merge every `Update` in the
message — and differ in the reply. `ping` answers with the receiver's records
for the members the message mentioned plus its own (SWIM's ping/ack, with the
dissemination riding on it); `sync` answers with the whole table
(memberlist's push/pull, the anti-entropy that repairs what a piggyback
missed). As in the other two services, **no method takes the sender's number**:
who is calling is the `Context`, and an `Update`'s `node` field names the
member being spoken *about*, which has to be content.

**Suspecting, declaring dead and refuting are not on the wire**, for the reason
Raft's `stand_for_election` is not on its: they are things a node does about its
own view, and putting them in the trait would let any caller make this node
believe anything. `Node::suspect` and `Node::declare_dead` are what the caller's
probe loop calls when a probe times out, and both take the incarnation the
probe or timer *began* with — a refutation can land while either is running, and
a timer that re-read the table would kill an incarnation nobody suspected; the refutation happens inside the merge,
the moment the record that changed is the node's own.

**The node writes nothing down, and that is deliberate.** Raft's server and the
ownership registry both keep a durable record because forgetting it breaks their
safety. Incarnations are self-correcting: a node restarted at incarnation 0,
whose peers remember it dead at 3, is told so by the first message that mentions
it, and answers with 4 (`a_restarted_node_is_told_what_it_was_and_outranks_it`).

`tests/swim_membership.rs` delivers one set of updates in all 120 orders, with
every message repeated, and checks the table is the same each time — S2, S4 and
S6 exercised through the service rather than assumed of it.
`tests/swim_turmoil.rs` runs SWIM's own story across a simulated network: a node
that cannot reach a peer suspects it, the partition heals, the suspicion reaches
the suspected node, which is alive and refutes it, and the refutation comes back
in the reply and clears the suspicion. `tests/swim_dynamic.rs` is the growing
cluster: a join is a first call and the reply is the cluster, a stranger the policy
refuses stays a stranger, a closed node still refuses to learn of members it was
not built with, a second address cannot speak as an existing member, the cluster
is bounded, a departure survives a late suspicion and a late `Dead`, a node does
not refute its own departure but does refute one it did not announce, and a
departed member returns at a higher incarnation. The same file's wire test in
`tests/swim_turmoil.rs` has a node join through a member that is not the first,
the rest hear of it by gossip, and a departure arrive as one.

**What the service does not have**, and what it does not claim. A caller is
identified by address, against the roster the node holds (fixed for `Node::new`,
growing by policy for `Node::admitting`), and *an address is not a
credential* (the stated assumption every service here makes) — and SWIM
sharpens it, because any member may gossip about any member, so a
member that lies about a third party is believed. SWIM's failure model is
crash faults, not Byzantine ones. There is no probe timer, no indirect-ping
fallback (`ping_req`), and no piggyback *budget*: a node sends what its caller
hands it. That loop — pick a peer, note its incarnation, wait out a timeout, call `suspect` with the incarnation it noted — is where
timing lives, and nothing in `swim::model` says anything about timing.
