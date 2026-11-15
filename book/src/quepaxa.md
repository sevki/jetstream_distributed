# QuePaxa: consensus without timeouts

[Raft](raft.md) gets one leader per term by counting votes, and replaces a dead leader by
waiting for a timeout. The timeout is the weak point. Set it too short and a healthy
leader is deposed, so progress stops while the cluster churns through elections. Set it
too long and a dead leader costs seconds. An adversary who can slow the leader's messages
can keep a timeout-based protocol from deciding at all.

QuePaxa (Tennage et al., SOSP 2023) is a consensus protocol with no timeout in its
liveness argument. Its core is a randomised asynchronous algorithm in which several
proposers may act at once and **help each other instead of getting in each other's way**,
so there is no view change to time out into. A designated leader still gets the usual
one-round-trip decision when the network is kind. Timeouts are not what the protocol
waits on; delays are only an optimisation for when to bother proposing.

## The round

Every round, each replica proposes its preferred value with a random priority. Replicas
then spread proposals in three steps, each handing a replica a set built from what a
majority told it:

```text
step 1:  P_i   the proposals i heard from some majority
step 2:  E_i   the union of what a majority heard in step 1   "exists" for i
step 3:  C_i   the union of what a majority learned in step 2 "common" for i
         U_i   something every replica's C contains            "universal" for i
```

Each replica adopts the best proposal in its `C_i` as its preference for the next round,
and **decides** if the best proposal it knows exists, `best(E_i)`, is also the best it
knows is universal, `best(U_i)`.

## Why it is safe, in one chain

The two guarantees the broadcast gives (a replica hears from a majority, and the relayed
set lands inside everyone's next set) make `U_i ⊆ C_j ⊆ E_k` for every `i`, `j`, `k`. If
`i` decides, its best proposal `b` is in `U_i`, so in every `C_j`, so in `E_i`. And `b` is
the best of all of `E_i`, so it is the best of every `C_j`. **Every replica adopts `b`**,
every later round proposes only `b`'s value, and no later decision can differ. That chain
is machine-checked: agreement, validity, and the fact that a decision is locked in
([Reference](reference/quepaxa.md#what-is-proved), Q1 to Q5).

## What is built, and what is not

Two pieces:

- **The abstract algorithm** over an ideal broadcast, with its safety proved and a proof
  that the model is not vacuous: when every replica hears from every live replica, every
  live replica decides.
- **The recorder's register.** In the concrete protocol, recorders are passive: each keeps an
  *interval summary register* and answers proposers' requests from it. The paper specifies
  it as if it kept its whole history, then observes four integers suffice. Both are here,
  and the four-integer one is verified to answer exactly what the history-keeping one
  answers, for any history the register stands for (Q8). A step the register has left behind never changes, and an
  aggregate never shrinks (Q9, Q10), which is what keeps a recorder's replies from moving
  under a proposer.

**Not built, and this is the claim that matters:** the concrete protocol, the proposers
that drive recorders and catch up when one is ahead. It is what is supposed to give the
abstract algorithm its broadcast. So the safety proof here says the *idea* is sound, and
does not say any implementation is. Also not built: termination (the paper proves it holds
with probability one, and this crate has no probability), the leader's fast path, the
hedging schedule, a log of slots, and any service. Nothing uses QuePaxa, and it is not
connected to [ownership](ownership.md)'s registry, which still assumes atomicity it does
not get from any consensus.

Next: [SWIM](swim.md), which does not try to agree on anything.
