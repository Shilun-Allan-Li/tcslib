<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.repeatRun_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Decomposition of Repeated Runs

**Claim.** If $t>0$ and $w$ has length at least $t$, the repeated-run procedure returns the left-biased optional choice between applying $q$ to the first $t$ bits and running the procedure on the remaining suffix.

**Proof.** The defining condition for the recursive clause holds: $t$ is positive and $t\le |w|$. Unfolding the definition in this case gives exactly the left-biased optional choice of $q$ on the first $t$ bits and the recursive run on the suffix.
