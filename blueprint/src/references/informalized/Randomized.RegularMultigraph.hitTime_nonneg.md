<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Truncated Expected Hitting Time

**Claim.** For every integer $N\ge0$, the cumulative miss probability through step $N-1$ is nonnegative.

**Proof.** Every miss probability is nonnegative. A finite sum of nonnegative terms is nonnegative, so the sum over steps $0$ through $N-1$ is nonnegative, including the empty sum when $N=0$.

**Key facts.** `Randomized.RegularMultigraph.missProb_mem_Icc`.
