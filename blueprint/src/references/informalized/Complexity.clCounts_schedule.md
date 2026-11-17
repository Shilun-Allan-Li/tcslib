<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCounts_schedule -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counts Match Scheduled Positions

**Claim.** On the input of $m$ false bits, the input-coordinate signed count plus one equals the input-head position at time $t$, and each work-tape signed count equals that tape’s head position.

**Proof.** Apply the equality between signed counts and reference positions (`Complexity.clCounts_positions`) to the input coordinate. There, the reference position is the input-head position shifted down by one, so adding one gives the asserted input-head position. Apply the same equality at each work-tape coordinate: the corresponding reference position is exactly that tape’s head position. The coordinate definitions then give both conclusions.

**Key facts.** `Complexity.clCounts_positions`.
