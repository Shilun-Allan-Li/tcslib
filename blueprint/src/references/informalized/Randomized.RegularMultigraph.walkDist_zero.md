<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.walkDist_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Step Walk Distribution

**Claim.** Walking for zero steps leaves a rational vertex weight function unchanged.

**Proof.** Fix a vertex $v$. By the zero-step transition formula, the transition probability from $u$ to $v$ is $1$ when $u=v$ and $0$ otherwise (`Randomized.RegularMultigraph.transProb_zero`). Therefore the defining sum for the new weight has only the term $u=v$ contributing, and its value is $p(v)$. Since this holds at every vertex, the two weight functions agree.

**Key facts.** `Randomized.RegularMultigraph.transProb_zero`.
