<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.one_div_pow_le_transProb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for a Prescribed Walk

**Claim.** If a sequence $w$ of neighbor indices takes the walk from $u$ to $v$, then the probability that a uniformly chosen sequence of the same length takes the walk from $u$ to $v$ is at least $D^{-\operatorname{length}(w)}$.

**Proof.** Among all sequences of neighbor indices of length $\operatorname{length}(w)$, the prescribed sequence $w$ is one that reaches $v$. Thus the set of sequences reaching $v$ contains at least one element. Its probability is its cardinality divided by the total number $D^{\operatorname{length}(w)}$ of sequences, and so is at least the reciprocal of that total.
