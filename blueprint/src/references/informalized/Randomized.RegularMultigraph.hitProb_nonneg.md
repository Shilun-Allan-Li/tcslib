<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.hitProb_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hit Probability Is Nonnegative

**Claim.** For a regular multigraph and vertices $s,t$, the probability that a uniformly chosen sequence of $k$ neighbor indices starting at $s$ visits $t$ is nonnegative.

**Proof.** The probability is a quotient whose numerator is the cardinality of a set of index sequences and whose denominator is a natural-number power, viewed in the rationals. Both are nonnegative, so the quotient is nonnegative.
