<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitStep_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Producer-Step Orbit

**Claim.** Starting from the retained state encoding for $x$, time zero, and an empty table, $t$ producer steps yield the retained encoding for $x$, time $t$, and the first $t$ visit rows.

**Proof.** We argue by induction on $t$. At time zero, the iterate is the identity, and the row table at time zero is empty, so the claimed encodings agree by their definitions. For the induction step, assume the claim at time $t$. One more producer step applied to that encoding retains $x$, increments the encoded time from $t$ to $t+1$, and appends the visit row computed from $x$ and the time-$t$ encoding (the producer-step state update, `Complexity.clVisitStep_state`). By the recursive definition of the first $t+1$ visit rows, this appended table is exactly the table for time $t+1$.

**Key facts.** `Complexity.clVisitStep_state`.
