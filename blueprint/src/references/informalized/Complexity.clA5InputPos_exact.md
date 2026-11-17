<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5InputPos_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Stored Input Position

**Claim.** For every cursor and every time within the stated producer horizon, the packed encoding stores exactly the machine's input-head position at that time on the corresponding all-false input.

**Proof.** Expand the stored-position formula: it is the count associated with the input-head coordinate, plus one, minus the count associated with its direction coordinate. The exact-count result (`clA5Count_exact`) identifies each of these two stored counts with the corresponding coordinate of the machine's trajectory counts, since the time lies within the producer horizon. The schedule identity (`clCounts_schedule`) says that the signed difference of those coordinates, plus one, is precisely the machine's input-head position. Substituting the two exact counts into the stored-position formula therefore gives the claimed equality; the remaining arithmetic is the rearrangement of this signed identity.

**Key facts.** `Complexity.clA5Count_exact`, `Complexity.clCounts_schedule`.
