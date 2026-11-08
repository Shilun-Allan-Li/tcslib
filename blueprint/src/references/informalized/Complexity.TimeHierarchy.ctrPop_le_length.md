<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrPop_le_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True Bits Bounded by Length

**Claim.** For every finite Boolean list $s$, the number of its true entries is at most its length.

**Proof.** Proceed by induction on $s$. The empty list has zero true entries and length zero. For a list $b::s$, if $b$ is false, its true-entry count and length each reduce to those of $s$, so the induction hypothesis gives the result. If $b$ is true, its count and length are each one more than the corresponding quantities for $s$, and the induction hypothesis again gives the inequality.
