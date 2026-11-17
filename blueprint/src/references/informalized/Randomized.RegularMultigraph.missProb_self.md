<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.missProb_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Miss Probability at the Target

**Claim.** For every vertex $t$ and every nonnegative integer $k$, a length-$k$ sequence started at $t$ has miss probability $0$ for the target $t$.

**Proof.** Separate the zero-length case from positive lengths. At length zero, the zero-step hit probability is $1$ when the starting vertex is the target (`hitProb_zero`), so the miss probability is $0$. For a positive length, the one-step recurrence for miss probability gives $0$ immediately when the starting vertex equals the target (`missProb_succ`).

**Key facts.** `Randomized.RegularMultigraph.hitProb_zero`, `Randomized.RegularMultigraph.missProb_succ`.
