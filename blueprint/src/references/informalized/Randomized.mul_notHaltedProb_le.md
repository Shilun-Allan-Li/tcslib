<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.mul_notHaltedProb_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonhalting Probability Bound

**Claim.** If halting is prefix stable and the sum of nonhalting probabilities over every finite initial interval is bounded by $B$, then $t$ times the length-$t$ nonhalting probability is at most $B$.

**Proof.** For each $s<t$, prefix stability implies that the probability of not having halted by time $t$ is at most the probability of not having halted by time $s$ (`Randomized.notHaltedProb_le_of_le`). Summing these inequalities over $s=0,\ldots,t-1$ bounds $t$ copies of the time-$t$ nonhalting probability by the sum of the nonhalting probabilities over that interval. The hypothesis `ExpTimeLe r B`, applied to the initial interval of length $t$, bounds this sum by $B$.

**Key facts.** `Randomized.notHaltedProb_le_of_le`.
