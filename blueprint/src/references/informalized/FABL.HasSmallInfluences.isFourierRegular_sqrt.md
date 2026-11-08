<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.HasSmallInfluences.isFourierRegular_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small Influences Bound Fourier Coefficients

**Claim.** If every coordinate has influence at most $\epsilon$, then every nonempty set $S$ of coordinates satisfies $|\widehat f(S)|\le\sqrt{\epsilon}$.

**Proof.** Take any nonempty $S$ and choose a coordinate $i\in S$. The squared Fourier coefficient on $S$ is at most the influence of any coordinate in $S$ (`sq_fourierCoeff_le_influence_of_mem`). The small-influences hypothesis, expressed as an upper bound on each ordinary influence (`hasSmallInfluences_iff`), makes this square at most $\epsilon$. Taking square roots yields $|\widehat f(S)|\le\sqrt{\epsilon}$.

**Key facts.** `FABL.sq_fourierCoeff_le_influence_of_mem`, `FABL.hasSmallInfluences_iff`.
