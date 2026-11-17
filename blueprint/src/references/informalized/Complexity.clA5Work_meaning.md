<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Work_meaning -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Constraint Meaning

**Claim.** The work constraint for tape $\tau$ at time $t$ holds exactly when the work slice of the time-$t$ block encodes blank if that position has not been visited before, and otherwise encodes the symbol written or kept there at the greatest earlier visit.

**Proof.** Split according to whether there is an earlier visit, as recorded by `prevVisit`. In either case, the work group is the corresponding group for the work predicate: the group evaluation theorem (`clA5Group_eval`) identifies its truth with that predicate. Unfolding the group and the two cases reduces the predicate to the displayed equality of the time-$t$ work slice with the blank encoding or the encoding of the symbol written or kept at the previous visit.

**Key facts.** `Complexity.clA5Group_eval`.
