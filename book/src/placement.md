# Where things run: placement and discovery

Two questions about location, and they are different questions:

| | Question | Trait | Answers with |
| --- | --- | --- | --- |
| **Discovery** | where does this thing live **now**? | `Discovery` | locations |
| **Placement** | where should this **new** thing go? | `Placement` | hosts, in order of preference |

Discovery may be stale and nothing depends on its being right. A request that reaches a
host that no longer owns the actor is answered `FENCED` by the fence in
[the services chapter](services.md), and the ownership epoch is what makes that answer
true. Discovery is an optimisation of where to look, not a source of safety.

## Discovery

`Discovery` has an associated `Resource` (what is being asked about) and `Location`
(what comes back), and one async method:

```text
discover(what: Resource) -> Result<Vec<Location>, DiscoveryError>
```

Two implementations exist, and they answer at different scopes:

- `LocalSupervisor` answers for **its own node only**. It is asked about an `ActorRef` and
  returns its own host id if the actor is `Running`. A draining, retired, stopped or absent
  actor is `NotFound`, which means "not here", not "nowhere".
- `QuicDirectory` answers with a **URL**, from a record of which host each placed actor
  was put on. See [the actor system](actor-system.md).

## Placement

`Placement` takes a resource and returns the hosts that should run it. The one scheduler
is the LAVA scheduler:

- It is the placement, scoring and ordering of the LAVA paper: placement (§4.3), NILAS
  scoring (§4.2) and LARS ordering (§4.4).
- Time is **caller-supplied**, monotonic. Exits are explicit events. A predicted expiry
  never removes a job.
- It knows hosts, their capacity and whether each is schedulable. It places a job, can
  migrate one, and can begin draining a host once an approval gate covers every job on it.
- A host can be made **unschedulable** without removing it. That is what the actor system
  does for a host membership suspects.

Around it, in the same area:

- **CRUSH** placement, behind its own feature because it is a dependency of its own. It
  is a stub.
- **Prequal** is not placement of actors; it picks which *replica* gets a *request*, by
  asking a few replicas how they are doing and sending to the one that looks best now. It
  is a pure decision: no sockets, no clock, no thread.
- **Monitoring** holds the Vivaldi network coordinates and a node's published, numbered
  resources. This book does not go into it.

## Evidence

All of this is **plain Rust, not verified.** The scheduling code is compiled into the
dependency-free build, but none of it is under Verus; the tests are the evidence. Of this
area, only `Id` and `IdSet` carry proofs. This chapter makes no claim of the kind the
protocol chapters do, and the protocols do not depend on placement being correct: a
badly placed actor is slow or unavailable, never doubly owned.

Next: [the actor system](actor-system.md).
