# Services over Jetstream

Each protocol also has a **service** that runs it over Jetstream RPC. The service calls
the verified step functions; it does not re-derive them. This chapter is about what a
service adds around a protocol, and the pieces that let several of them share a node.

## The shape every service has

- **The decision is a verified function; the service is the part around it.** Who is
  calling, what a message carries, the lock, the audit log, the batch limit. The
  steps (`steps_v.rs`, `exec_v.rs`) are verified; the service files are plain Rust that
  Verus never sees, and the tests exercise them.
- **Identity comes from the connection, never from an argument.** No method takes the
  acting node's number. The caller is the transport's `Context`. This turns a whole
  class of "the message lied about who sent it" from a guarded-against bug into an
  unrepresentable one.
- **Today that identity is an address against a roster**, and an address is not a
  credential. The roster is fixed at construction everywhere except SWIM, whose node can
  also be built to admit new addresses by a policy (see [SWIM](swim.md)). The shape survives replacing it with a TLS or key identity.
- **One gate across a decision.** A decision that reads the registry and then writes
  the journal holds one lock across both. Two locks taken one after the other would leave
  the gap that fencing exists to close.

## Fencing a running actor

The actor's journal write is fenced by [ownership](ownership.md). A *running service*
needs the same fence at the other end: a host that has lost the actor must stop acting
for it.

`Fence` is the question "may this host still act for its actor?". The intended answer is
the ownership registry's own `may_write(host, epoch)`, which turns false the moment the
epoch moves on, whether the owner handed the actor over or had it taken. Any
`Fn() -> bool` is a fence.

`serve_fenced` asks it **before each request**:

- A request the fence refuses is answered `FENCED` and is never handled.
- A handler that is already running is **finished**, not cancelled.
- Delivery is **at least once**. A caller that gets `FENCED` may have had an earlier
  request run.

This is **tested, not proved.** The fence itself, the ownership check, is the proved part.
What is checked here is that the loop around it does what its documentation says.

## The supervisor

A `Supervisor` owns what runs **on this node**. `LocalSupervisor` hosts any number of
actors, each as a service behind its own [mailbox](mailbox.md):

| Status | Meaning |
| --- | --- |
| `Running` | serving requests; the only status that is handed out a new session |
| `Draining` | a drain was asked for; the running handler is finishing |
| `Retired` | drained: the service is dropped, the mailbox remains and answers `FENCED` |
| `Stopped` | the handler panicked; the drain task is gone |
| `Absent` | never hosted here |

Three properties worth knowing:

- **`spawn` requires a fence.** An actor with no way to be told it has lost the actor
  is not something this node will host.
- **A restart over `Stopped` or `Retired` reuses the same mailbox** when the protocol
  matches. A session obtained before still works, and queued requests are not stranded.
- **`transport` returns a session onto the mailbox**, a `Box<dyn ClientTransport<P>>`,
  so a caller builds an ordinary generated channel and cannot tell a local actor from any
  other.

## Draining

`drain` is a cooperative stop. It closes the actor's fence, waits for the running
handler to finish, drops the service, and returns. The mailbox is kept, with a small task
answering every request `FENCED`, so a session made before the drain is told rather than
left waiting.

Two details that came from review and are worth keeping in mind:

- Retirement is raced against *waiting for work* and nothing else, so it can never
  cancel a handler. It is also checked once more between rounds, because the mailbox is
  polled first and a backlog would otherwise starve a ready retire signal for ever.
- A handler that panics while the actor drains makes it `Stopped`, and `drain` reports an
  error instead of claiming a release that did not happen.

## Not here

- **Nothing decides *when* to drain.** The mechanism exists; the policy does not.
- **The retrying caller.** A `FENCED` answer means "ask where the actor lives now". No
  caller yet asks discovery again and retries.
- **Tying the fence to a registry, host and epoch.** The fence is a closure the caller
  supplies; nothing here constructs it from the ownership registry.

Next: [Where things run](placement.md).
