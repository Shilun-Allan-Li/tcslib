<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Snapshot.lean :: Complexity.prevVisit_some_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterisation of the last previous visit

**Claim.** If $s$ is the last time before step $t$ when tape $\tau$'s head occupies its position at step $t$, then $s<t$, the head positions at $s$ and $t$ agree, and at every intermediate time $r$ with $s<r<t$ the position differs from the position at $t$.

**Proof.** The maximum characterization of a defined maximum (`List.max?_eq_some_iff`) says that $s$ is a member of the filtered list and that every member of that list is at most $s$. Membership gives both $s<t$ and equality of the head positions at $s$ and $t$. Now let $s<r<t$ and suppose the positions at $r$ and $t$ agreed. Then $r$ would also belong to the filtered list, so maximality would imply $r\le s$, contradicting $s<r$. Thus every intermediate position differs from the position at time $t$.
