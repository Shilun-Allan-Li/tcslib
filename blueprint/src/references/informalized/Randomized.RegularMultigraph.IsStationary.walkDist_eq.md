<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.IsStationary.walkDist_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationarity under repeated walks

**Claim.** If one step of the random walk preserves the rational-valued distribution $p$, then every nonnegative number of steps preserves $p$.

**Proof.** Proceed by induction on the number $k$ of steps. At zero steps, the walk distribution is exactly the starting distribution, by the zero-step identity (`Randomized.RegularMultigraph.walkDist_zero`). For the induction step, the distribution after $k+1$ steps is the $k$-step walk distribution started from the one-step distribution (`Randomized.RegularMultigraph.walkDist_succ`). By stationarity that one-step distribution is $p$, and by the induction hypothesis the resulting $k$-step distribution is again $p$.

**Key facts.** `Randomized.RegularMultigraph.walkDist_zero`, `Randomized.RegularMultigraph.walkDist_succ`.
