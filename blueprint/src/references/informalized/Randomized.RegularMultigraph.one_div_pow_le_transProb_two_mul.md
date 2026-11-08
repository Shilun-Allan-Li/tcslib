<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.one_div_pow_le_transProb_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound on Transition Probabilities

**Claim.** For a finite connected regular multigraph of positive degree that is not bipartite, the probability that a uniformly chosen sequence of $2|V|$ neighbor indices takes the walk from any $u$ to any $v$ is at least $D^{-2|V|}$.

**Proof.** Connectedness and non-bipartiteness ensure that there is a sequence of neighbor indices of length exactly $2|V|$ taking $u$ to $v` (`exists_endpoint_eq_two_mul`). For any prescribed sequence that reaches $v$, its transition probability is at least the reciprocal of the number of possible sequences of that length (`one_div_pow_le_transProb`). Substituting the sequence's length, which is $2|V|$, yields the claimed bound.

**Key facts.** `Randomized.RegularMultigraph.exists_endpoint_eq_two_mul`, `Randomized.RegularMultigraph.one_div_pow_le_transProb`.
