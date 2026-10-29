# The protocol as a Jetstream service

**Every algorithm in this repository has a service**, and each is a `#[service]
trait` over Jetstream RPC implemented by a type that holds the algorithm's state
behind one lock and calls the algorithm's verified step functions:

| Algorithm | Trait | Implemented by | Executable steps | What the trait leaves off the wire |
| --- | --- | --- | --- | --- |
| ownership | `Ownership` | `Registry` | `ownership::steps` | `force` — the coordinator's own transition |
| Raft | `Consensus` | `Peer` | `raft::steps` | standing for election, tallying votes, taking a term |
| SWIM | `Swim` | `Node` | `swim::steps` | suspecting, declaring dead, refuting |
| Raymond | `Routing` | `Router` | `raymond::steps` | — (every method acts on the caller's own entries) |
| composed | `Composed` | `Coordinator` | `composed::steps` | seizing the privilege |
| actor | `Actor` | `Host` | `actor::steps` | `force` — the coordinator's own transition |

The shape is the same each time, and so is what it buys: **no method takes the
acting node's number**, because who is calling is the `Context` and a caller
cannot forge it; and what a node does *to itself* is not something a peer can
ask it to do on the wire. The sections below go through ownership in detail, and
SWIM has its own [service section](swim.md#the-service); Raymond and the composed
machine are summarised here.

Everything above is a model and a simulation of it. `src/ownership/service.rs` is the
protocol served over [Jetstream](https://github.com/sevki/jetstream) RPC — a
`#[service] trait Ownership` with `poll`, `acquire`, `write`, `begin_transfer`
and `release`, implemented by a `Registry` that performs the fence with
`ownership::exec::FenceGuard`.

**The service form removes a class of defect rather than guarding against it.**
The line protocol in `tests/` carries the sender as a field — `WRITE 0 41`
*claims* to be node 0 — so the registry has to be told to believe the connection
rather than the claim, and every request is a place to get that wrong. Four
rounds of review on that suite were spent hardening exactly that rule. Here no
method takes a node number at all. Who is calling is the `Context`, which
Jetstream fills in from the transport: *"The context is the transport's, not the
frame's"* (`jetstream_rpc::server`). A caller cannot forge it, so "the line lied
about who sent it" is not defended against — it is unrepresentable.

`force` is absent from the trait for the same reason. It is the coordinator's
own transition, and the line protocol needed a dedicated control connection to
stop a node sending it; a node-facing service simply does not offer it.

**The assumption, stated rather than assumed.** `Context::peer()` is the
authenticated identity and is `None` over plain TCP — jetstream's own comment
says a plain stream authenticates nothing. The authenticated forms are a TLS
certificate or an iroh `NodeId`, and `NodeId`'s value is private with no
accessor outside `jetstream_rpc`, so neither is usable yet. The service
therefore identifies a caller by address, against a roster fixed at
construction. **An address is not a credential.** In a simulated network nothing
can spoof one; on a real network it is worth very little. Replacing it with TLS
identity is the first thing to do, and what does not change when it is replaced
is the shape: identity arrives with the connection, never in an argument.

**Neither durable nor replicated — and one of those is now fixed.** The
registry's state lives in an `Arc<Mutex<..>>`, which supplies the *atomic* half
of the model's strongest assumption and none of the *durable* half. That gap is
not a tidiness problem: every fencing theorem assumes epochs only go up, and a
registry that comes back not knowing where it was can offer an epoch it already
burned. A partitioned owner still holding that epoch is then unfenced — not
because the fence failed, but because it was asked about a world that had been
rewound.

So the starting epoch is no longer a number from the caller. It is read from an
`EpochFloor`: a durable, monotone high-water mark of every epoch the registry
has ever used. `Registry::new` starts strictly above it and writes that down
before serving, and each later burn is recorded *before* the state depending on
it is visible, so a registry that dies mid-decision skips an epoch — the safe
direction, since epochs must not repeat but need not be consecutive.
`tests/ownership_durability.rs` runs the same handover against a floor
that remembers and against one that forgot, and asserts in the second case that
the already-fenced owner writes again at the burned epoch while the node holding
the *later* epoch is the one refused.

What is still missing is replication. Two registries sharing one floor would
both read it and both believe they had allocated the next epoch: durability and
atomicity want to come from the same place, which is why the row above says a
real deployment keeps the ownership record in a store with compare-and-swap.
This is the same class of caveat as the address-identity one, and it breaks the
same guarantee.

**What is verified about it, precisely.** Every decision the service makes about
the actor and every grant it publishes, and nothing else. `poll`, `acquire`,
`write`, `begin_transfer`, `release` and `force` each go through a method of
`ownership::registry::RegistryCore`, which hands the actor's record to a function in
`jetstream_distributed::ownership::steps`, stores what comes back, and publishes the
grant the model's transition publishes (E8–E9). The step functions are
executable `u64` code with postconditions stated in terms of the model, and
`ownership::proofs::refinement` is where the postconditions are tied to `tr_acquire`,
`tr_begin_transfer`, `tr_handle_revoke`, `tr_complete_release`,
`tr_revoke_owner`, `tr_reassign_unowned`, `tr_abort_transfer` and
`tr_issue_grant` — rows E1 to E6 above.

Two things are worth being exact about. First, the refinement is stated in both
directions where the notion makes sense: a step function that refused everything
would satisfy "whenever it fires, the model steps" perfectly, so the theorems
also say that a refusal means the model's step is *not enabled*. Second, what is
left outside is named rather than left to be discovered: **the lock, the identity
lookup, the durable epoch floor and the audit log are not verified.** They are
the server's business, and a step function that also resolved identity would
have quietly folded an unverified lookup inside a verified transition.

The couplings that connect one actor's `u64` record to a whole `System` are
hypotheses of the theorems rather than silent assumptions — the registry's
issued-grant set stands for `network.contains(Grant { .. })`, its roster for
`nodes.contains(..)`, an open connection for `live.contains(..)` — and the
module docs of `ownership::proofs::refinement` tabulate which part of the service
discharges each one.

The grant coupling is the one a server can *break*, and one did. `granted` is
an **input** to the verified acquire step, so the registry's set has to hold
every grant the model's network would — and **four** transitions publish one,
not just the poll: `tr_complete_release`, `tr_revoke_owner`,
`tr_reassign_unowned` and `tr_abort_transfer` each offer the actor on as part of
moving it. A registry that recorded only the poll's grant was applying the
refusal theorem under a hypothesis that did not hold, which is worth nothing at
all. The visible symptom was much smaller than the real one: a node that took
the actor without polling first was refused, although the model had already
published its grant.

**Status.** The service is pinned to the Jetstream working tree rather than to a
release — `16.3.1` is not on crates.io, which the dependency resolution caught.
Its dependency graph resolves, but the environment it was written in cannot
reach crates.io's tarballs, so **CI is the first place it is compiled**. That is
the same footing the fuzz target was on when it was added, and it is stated here
rather than discovered.

## Raymond and the composed machine

**The record is verified code; the shell is not (R16–R17).** `Router` keeps an
`exec::RayTable` behind its lock, and every routing method goes through it, so each
is the model's step by contract and each refusal is a step the model could not take.
What is not proved: building the table (`new`, `add_node`) is not a model step, and
that the finished table is `ray_init` — every other node points somewhere, the
pointers reach the root — is checked by `Router::new` at start-up; the roster (which
connection is which node), the lock, the audit log, and who may call `seize` and
`reconcile` (the composed coordinator, which checks the token) are plain Rust the
tests exercise.

**Raymond's `Router` hosts the whole routing record in one process**, the way the
ownership `Registry` hosts `System::actors`. That is the model's own shape —
`Raymond` is one struct — and it is what lets the router tell `privilege` (where
the privilege *is*) from `holder` (what a node *believes*), the split the whole
stale-holder analysis rests on. It is also a limit worth saying plainly: **this
checks Raymond's rules, it does not distribute them.** A deployment where each
node keeps only its own entries and messages carry the rest is a different
system with a different failure model, and nothing in `raymond::model` says it
is refined by this one. `Routing` has one method per labelled model step a node
takes (`request_cs`, `make_request`, `receive_request`, `assign_privilege`,
`enter_cs`, `exit_cs`), each acting on the caller's own entries.
`receive_request` does take a `from`, and that is not the same thing as naming
the acting node: it is the node the request is *about*, checked against the
router's own record of what has been sent, so naming a node that never sent one
is refused rather than believed.

**The composed `Coordinator` is the two services and the guards between them.**
Almost all of it is delegation, because `cs_own` and `cs_ray` carry a step the
layers have already proved (C9). What it adds is the coupling: the privilege moves
only once the actor has been released (`assign_privilege`), authority is taken
only by the node holding the privilege (`acquire`), and the privilege can be
seized from a holder that does not cooperate (`Coordinator::seize_token`,
inherent — no node may cause it) leaving that holder owing a reconciliation
(`reconcile`). Every method takes one **gate** first, because the coupling reads
both layers' state in one decision: with two locks taken one after the other, an
`acquire` could slip in between the registry's "unowned" and the privilege
moving, stranding authority at a node that no longer holds the privilege.

**What the composed service does not claim.** The composed *model* guards some
steps on `own.live`, which is ground truth — whether a node has crashed is not
something any process can evaluate. The service has no `Crash` or `Recover`, so
the steps it calls refine the composed machine's **crash-free** executions, where
every liveness guard is vacuously true (the service around those steps is plain
Rust and tested); C8 states `live.contains(..)` as a hypothesis rather than
dropping it. That cut does not lose the case the machine exists for:
`SeizeToken` has no liveness guard on the node it takes the privilege *from*, so
seizing from a holder that is merely unreachable — the wrongly-suspected node a
real coordinator cannot tell from a dead one — is inside the fragment. And a
standalone `Router` never creates a stale holder; seizure is the composed
machine's step, because the revocation that justifies it is visible there.

`tests/raymond_routing.rs` runs the textbook request path (`D -> B -> A -> C` and
the privilege back) and every refusal; `tests/composed_handover.rs` checks the
refusals that make the composition mean something — the privilege will not move
while the actor is held, a node offered the actor without the privilege cannot
take it, a seized holder is fenced and must reconcile. `tests/raymond_turmoil.rs`
and `tests/composed_turmoil.rs` run the same stories across simulated hosts, one
host per node, so the coordinator learns who is acting from the connection.

## The actor

`actor::service::Host` holds an actor's journal and a mailbox of what has been sent,
and **fences every append with the ownership `Registry` it is built around** — the
same registry, with the same epoch floor, that the `Ownership` service serves. The
actor adds nothing to the ownership protocol; it *uses* it. Four of `Actor`'s
methods are the ownership calls, delegated (`poll`, `acquire`, `begin_transfer`,
`release`); the others are `send` (the caller numbers its own messages, so a retry
after a lost reply is the same message), `accept`, two reads (`state`, `journal`),
and `receive`, which ends at once because the model's actor has no outputs.
`accept` takes the `sender` whose message is being processed, and that is not the
same thing as naming the acting node: it is checked against the mailbox, so a
message that was never sent is refused rather than believed.

An append reads the registry (is this host the owner at this epoch?) and writes the
journal, so the registry is **built inside `Host::new`** from the one roster and
every method takes a **gate** first — the same construction, for the same reason, as
`composed::service`. The fence is asked first and about the registry's own record
(`Registry::may_write`, which is `may_write_step`, which is `can_mutate`), so a host
that is not the owner learns nothing about the journal. The behaviour is applied by
the service, not the host: `accept` returns the state it produced, and a host that
has just taken the actor catches up by reading the **journal**, not a copy of the
previous host's memory.

**What the actor service does not claim.**

* **Its journal is in memory.** The model assumes the journal is durable and linear
  — it has no crash that loses an accepted entry — and the service does not meet
  that: a restarted `Host` has an empty journal and an epoch floor that remembers
  only epochs. Durability is the next layer, and `raft::store`'s record store is the
  shape it would take. Until then the guarantees hold for the lifetime of the
  process, and not across its death.
* **Crash-free executions only**, as in `composed::service`: no `Crash` or
  `Recover`, because liveness is ground truth a process cannot evaluate.
* **The behaviour is a pure fold.** The model's `apply` is a function from state and
  message to state, taken modulo a machine word so the executable version is not
  narrower. A real actor performs effects when it handles a message; nothing here
  says what an effect does if its host is fenced halfway through. The guarantee is
  about the *journal*, which is where the fence is.

`tests/actor_journal.rs` runs the guarantees through Jetstream — every call goes over
a generated client channel and session to the generated server in front of the
`Host` (`Host::pipe`, an in-memory stream whose peer address the caller names, as a
TLS adapter supplies its handshake's identity) — redelivery,
messages ahead of their turn, the fence asked first, a handover that keeps the
journal and fences the old host, a forced revocation, and all 24 orders of four
messages from two senders each attempted twice, checked to give a well-formed
journal whose state is the fold of whatever it holds. `tests/actor_turmoil.rs` runs
the whole story across simulated hosts: a sender sends, the owner accepts, the
actor is handed to another node, the old owner — still believing — is refused, and
the new owner catches up from the journal.

## Over any byte stream

`Host::serve(io, peer)` serves one connection over any `AsyncRead + AsyncWrite`
stream, and `Connection::new(io)` is the client end: TCP, turmoil, QUIC or an iroh
stream pair all fit. The one thing a stream may not be able to say is who is on the
other end, so `serve` takes it as the peer `Context` — an accept loop reads it off the
socket, a TLS adapter supplies its handshake's identity — and the host believes it,
so it must come from the transport and never from the peer. `Host::pipe` is the same
wiring over an in-memory stream, for tests and examples, where the caller names the
peer. The roster that maps a peer to a node is still keyed on `IpAddr`, so only
`RemoteAddr::IpAddr` identities are accepted today.

A `Connection` owns the session as well as the channel, and has to: dropping a
`SingleLaneSession` cancels its lane.

## The mailbox as a transport

The mailbox of the previous section is what a call goes *through*, not something a
caller sees. Given `#[service] trait ActorB`, a caller holding an `ActorB` — a
generated `ActorBChannel`, or the implementation itself — writes `self.b.b(ctx).await`
either way and cannot tell which:

```text
caller ── ActorBChannel ── Session ──▶ Mailbox ──▶ serve ── ActorBService ── impl
                              ◀── reply ──────────────────────┘
```

* **`Mailbox<T>`** is the protocol's six steps on real threads, each method one model
  step under one lock: a sender's `enqueue` (through a `Permit`), `set_state` and
  `schedule`, and the drain's `claim`, `take` and `finish`.
* **`Session<P>`** is a `ClientTransport`, which is all a generated channel asks of
  what it sits on. `poll_ready` reserves a slot, `start_send` enqueues, and
  `poll_flush` runs the rest of the sender's operation, which is where the drain is
  woken.
* **`serve(mailbox, &mut service)`** is the drain. It takes rounds from the mailbox
  and hands each request to the service in the order queued, one at a time, so the
  service sees one request at a time and each sender's requests in the order it sent
  them. Identity is read off the delivery, not the lane: a mailbox has many senders
  and one drain, and `Server::rpc` takes the `Context` per call. A request in flight
  when the drain is aborted is answered with an error, and only that one.
* **`serve_fenced(mailbox, &mut service, &fence)`** is `serve` asking a `Fence`
  before it starts each request. A request the fence refuses is answered `FENCED`
  to its sender and never reaches the service; the drain goes on, so a host that
  regains the epoch serves again. The fence is meant to be the registry's
  `may_write(host, epoch)` about the host's own claim, so it turns false when the
  epoch moves, whether by `BeginTransfer` or `RevokeOwner`. It is checked
  *between* requests: a handler already running finishes, so a handover waits for
  nothing. **Tested, not proved** (`tests/actor_fence.rs`): the ownership fence is
  proved, that this loop asks it first is not. What a running handler does outside
  the fence, the fence cannot stop, and a request that ran but whose reply was
  lost will be retried at the new owner (at-least-once).
* **`Supervisor`** owns the actors that run on a node (`LocalSupervisor` is the
  in-process sketch): `spawn` takes a **required** `Fence` and serves through
  `serve_fenced`, `status` says `Running`, `Stopped` (the handler panicked, so the
  drain ended) or `Absent`, and spawning over a `Stopped` id restarts it. *Where* an
  actor lives is the scheduler's existing `Discovery` trait asked about an
  `ActorRef`; a supervisor answers for its own node only. Discovery may be stale and
  nothing relies on it: a request to a host that no longer owns the actor is
  answered `FENCED`. What the caller then does is **not implemented here**: a caller
  is expected to ask Discovery again and retry, and no caller in this slice does
  (the fence test checks only that `FENCED` comes back). Restarting a `Stopped` actor
  reuses its mailbox when the protocol is the same, so sessions obtained before the
  stop, and the requests already queued, reach the new drain; until it is restarted
  they wait, and a new `transport` is refused. **`drain(id)` is the cooperative
  stop**: it closes the actor's fence (so it starts nothing, and what is queued is
  answered `FENCED`), waits for a handler that is already running to *finish*, drops
  the service, and returns; the status goes `Running`, `Draining`, `Retired`. The
  mailbox is kept, with a small task on it that answers every request `FENCED`, so a
  session made before the drain is told rather than left waiting, and `spawn` over a
  `Retired` actor takes the same mailbox over. A handler that panics while the actor
  drains makes it `Stopped`, and `drain` says so. Delivery stays at-least-once: a
  request that ran but whose reply was lost is retried at the new owner. **Tested,
  not proved** (`tests/actor_supervisor.rs`, `tests/actor_drain.rs`). Not here: a
  lane to a remote host, the retrying caller, *who* decides to drain (a composition
  with the ownership layer), and tying the fence to a registry, host and epoch.
* **Backpressure.** A mailbox is built with a `Capacity`, which is always the
  caller's to say: `Bounded(n)` makes `poll_ready` wait for a free slot (the drain
  wakes it), `Unbounded` never does, and there is no default and no number that
  means "no limit". The model's queue is unbounded and a full mailbox is a sender
  that has not begun its operation, which the model reads as a stutter — so the
  safety proofs carry over, and the liveness theorem owes progress only to
  operations already begun. That is an argument about the mapping, not a proof.

**What it does not claim.**

* **Only the core is a refinement.** Verus checks `exec::MailboxCore` against the
  model (MB10–MB11); it does not check the lock, capacity, permits, wakers or
  notification around it, `requeue`, or that callers follow the sender's three
  steps. Those rest on the tests (`tests/actor_mailbox.rs` and the unit tests in
  `mailbox.rs`: many senders into a small mailbox lose nothing and keep their order,
  a full one holds its callers back and not its queue, and an aborted drain answers
  only the request it dropped).
* **`serve` does not check the ownership epoch.** It hands each request to the
  service. The fence belongs around `Server::rpc`, and `Host` does not sit behind a
  mailbox yet.
* **A bound is a place to deadlock, and a cycle already is.** The drain runs one
  message at a time, so a handler waiting on an actor whose handler is waiting on it
  holds both drains whatever the capacity. A bounded mailbox adds a way in: a sender
  inside a handler waiting for a slot. Do not wait on another actor inside a turn
  that another actor can be waiting on.
* **No subscriptions.** Streaming methods are served by `jetstream_rpc`'s `run` on a
  lane; a mailbox delivers one request and takes one response. The reply path from
  the drain to each session is not bounded.

`cargo run --example actor_basic` runs two actors, each behind its own mailbox, with
the first calling the second.
