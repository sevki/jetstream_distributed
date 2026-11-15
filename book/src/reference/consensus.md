# Consensus: one interface, tested of each protocol

[Raft](raft.md) and [QuePaxa](quepaxa.md) reach agreement in unrelated ways. A consumer
should depend on neither, so `src/consensus/mod.rs` defines **one interface,
`ReplicatedLog`: a log that every replica agrees on.** `propose(value)` returns the slot
the value was decided at, `decided(slot)` what was decided there, `committed()` how many
slots are decided with no gaps. Both protocols implement it: `quepaxa::service::QuePaxaLog`
and `raft::replicated::RaftLog`. Raft's own wire trait is `RaftRpc`; it is the protocol's
messages and not a second consensus interface.

This page says what is claimed about the interface, which is **tested and not proved**.

| ID | Claim | Evidence | Assumes |
| --- | --- | --- | --- |
| C1 | **Six properties hold of every implementation:** agreement (two replicas that report a slot report the same value), validity (a decided value was proposed), a decision is visible to the replica that returned it *as it returns*, two different values never share a slot, `committed` is a prefix of decided slots, and a decision never changes | `tests/consensus_contract.rs`: `obeys_the_contract`, written against the trait and run on both, with no failure, with calls lost (up to 45% for Raft), with a crashed minority and with five proposers at once | crash-stop with fewer than half failed; the in-process fault injection in the test |
| C2 | **A cluster in which nothing fails does decide**, on both. Termination is **not** part of the contract: an implementation may refuse (`ProposeError`), and whether it eventually succeeds is each protocol's own claim | the same tests | as C1 |

## What is not claimed

* **No theorem.** The two protocols prove different things of different models: Raft's
  Election Safety and Log Matching are proved and its Leader Completeness and State
  Machine Safety are not; QuePaxa's agreement is proved over an ideal broadcast. There is no
  specification both instantiate, because a shared theorem would have to hide that.
* **That the tests can catch what they do not check.** A mutant of `RaftLog` that returned
  from `propose` before the entry was committed survived the contract until the
  visible-as-it-returns check was added to `propose_somewhere`; the check is now there. Other
  mutants may survive.
* **Raft's timing.** `RaftLog` gives up on a follower after a per-call timeout and has no
  election timer: `elect` is what a timeout would call, and nothing calls it. QuePaxa has no
  timeouts at all. Neither's liveness is proved.
* **Values are `u64`**, a batch id or a command handle; what it means is the consumer's.
