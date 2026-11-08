<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.missProb_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on Miss Probability

**Claim.** For every nonnegative integer $k$, the probability that a length-$k$ sequence of uniformly chosen neighbor slots, started at $s$, fails to visit $t$ lies between $0$ and $1$, inclusive.

**Proof.** The miss probability is $1$ minus the hit probability. Since the hit probability is nonnegative and at most $1$ (`hitProb_nonneg` and `hitProb_le_one`), subtracting it from $1$ gives a quantity between $0$ and $1$.

**Key facts.** `Randomized.RegularMultigraph.hitProb_nonneg`, `Randomized.RegularMultigraph.hitProb_le_one`.
