<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitProb_eq_zero_of_not_reachable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unreachable Vertices Have Zero Hit Probability

**Claim.** If $t$ is not reachable from $s$ by a finite walk in a regular multigraph of positive degree on a finite vertex set, then for every $k$, the probability that a uniformly chosen sequence of $k$ neighbor indices starting at $s$ visits $t$ is zero.

**Proof.** Any index sequence counted by the hit probability would, by the fact that a successful sequence of indices yields a finite adjacency walk (`reflTransGen_of_hits`), witness that $t$ is reachable from $s$. This contradicts the hypothesis. Hence the set of successful sequences is empty and its cardinality is zero; dividing that count by the number of sequences gives hit probability zero.

**Key facts.** `Randomized.RegularMultigraph.reflTransGen_of_hits`.
