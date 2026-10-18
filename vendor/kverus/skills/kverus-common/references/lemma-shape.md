# Lemma Shape

Source scope: from KVerus proof practice

Create a helper lemma when:

- The proof is reused at multiple call sites.
- The proof needs induction.
- The local context is too large or unstable.
- The desired fact is a clean mathematical property of a spec function.

Keep lemma contracts narrow and pass only variables mentioned in the fact or needed preconditions.
