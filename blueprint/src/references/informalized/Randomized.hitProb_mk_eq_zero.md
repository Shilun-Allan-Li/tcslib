<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.hitProb_mk_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Hitting Probability at an Isolated Vertex

**Claim.** If distinct vertices $s,t\in\mathrm{Fin}(n)$ satisfy that $s$ has no outgoing neighbors, then the $k$-step probability of hitting $t$ from $s$ is zero for every natural number $k$.

**Proof.** Use induction on the number of steps. At time zero, the probability is zero because $s\ne t$. For the successor step, the hypothesis that the outgoing-neighbor set has cardinality zero implies that it is empty. Thus the averaging rule uses its empty-neighborhood case, which leaves the value at $s$ unchanged. The induction hypothesis says that this value is zero, completing the induction.
