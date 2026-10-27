# The actor system over QUIC

`ActorSystem` is what puts the previous chapters in order for a caller who wants to talk
to an actor and does not care where it is.

## Four things in one trait

An actor system has:

- a **supervisor**, which says what runs *here* and hands out a transport onto a local
  actor's mailbox;
- a **discovery**, which says where an actor *lives*, as locations;
- a **placement**, which decides which host should run something *new*;
- a **dial**, which opens a transport to a location. This is the one part that is specific
  to a transport.

`connect` is the one thing the trait adds, and the **order** it asks in is not the
implementer's to re-decide:

1. If the supervisor says the actor is `Running` here, hand out a session onto its mailbox.
   A local actor needs no network and no lookup.
2. Otherwise ask discovery, take the first location, and dial it.

What comes back is a `Box<dyn ClientTransport<P>>`, the same thing the supervisor returns,
so the caller builds an ordinary generated channel on it and cannot tell a local actor
from a remote one.

## The QUIC system

`QuicActorSystem` dials over QUIC:

- one connection per location, opened on first use and reused while it is alive; a closed
  one is dropped and replaced;
- each `dial` opens a **bidirectional stream** on that connection, which is the lane;
- a name can resolve to several addresses, so each is tried in order and the last failure
  reported;
- a handshake timeout, because QUIC is over UDP and an address nobody listens on is not
  refused.

`QuicActor` is a handle that forwards the actor protocol over whichever transport
`connect` found. It is tested over a real QUIC handshake on loopback.

## Placement feeds discovery

`QuicDirectory` is both the placement and the discovery. It holds three things: each
host's address, the host each placed actor was put on, and the scheduler.

- `add_host(id, capacity, url)` registers a host with the scheduler and its address
  **together**, so a host that can be chosen can be reached.
- `place` asks the scheduler, then records the chosen host for the job's actor. A job's id
  is the actor's. If the scheduler chose a host with no address, the job is taken back out
  and the placement is refused.
- `discover` answers from that record, looking the address up by host.

The record is a **cache of the placement** and is not kept in step with it. An actor that
has exited or moved stays where it was put until placed again, and a caller that goes to
the old address is answered `FENCED`.

## Membership as a hint

[SWIM](swim.md) tells the directory which hosts look gone:

| Membership says | The directory |
| --- | --- |
| `Suspect` | places nothing new on the host; what is already there is still found, because a suspect host may be fine |
| `Dead` or `Left` (the host announced its departure; treated alike, since either way its actors have to go elsewhere) | no longer places on the host, no longer finds what was placed on it, and **returns its jobs** to the caller |
| `Alive` again | places on it again, empty |

A host is made placeable again only if the directory is what made it unplaceable, so a
host drained for a migration is not switched back on by a rumour that it is alive. Each
step is idempotent, so reading the same view twice changes nothing the second time.

**Nothing moves an actor.** The jobs of a host that left come back for the caller to place
again or not. Placing them again starts a second copy if the host was only partitioned.
What keeps that from corrupting anything is the ownership epoch, which only one of the two
copies holds. That is [ownership](ownership.md), not this.

## What is not here

- **One actor service per host.** A dial reaches the actor service a host serves. Nothing
  on the lane says *which* actor. The settled direction is that an envelope carries the
  receiver's id as well as the sender's, so one connection can carry several actors; the
  other calls (`poll`, `acquire`, `accept`, `state`, `journal`) name no actor yet either.
  That is not built.
- **Nobody drives the membership view on a timer**, and the SWIM node has no change
  notification, so the view is polled.
- **SWIM's roster is keyed by address**, so mapping a SWIM node to a host here relies on
  both using the same `Id` for a host.
- **The Iroh system is entirely commented out.**
- **No automatic failover**, and no retrying caller that re-asks discovery on `FENCED`.

## Evidence

Plain Rust, tested, not proved. The tests include a real QUIC handshake, the placement
path, every membership step including that a drained host stays drained, and one run
against a real SWIM node that follows it from suspect to dead to refuted.
