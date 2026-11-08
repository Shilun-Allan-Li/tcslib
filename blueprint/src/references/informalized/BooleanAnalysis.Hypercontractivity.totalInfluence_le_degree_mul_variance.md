<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.totalInfluence_le_degree_mul_variance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence bound by degree and variance

**Claim.** If $f$ has Fourier degree at most $k$, then its total influence is at most $k$ times its variance.

**Proof.** Rewrite total influence as the sum over Fourier sets $S$ of $|S|\,\widehat f(S)^2$, using the Fourier formula for total influence (BooleanAnalysis.totalInfluence_eq_sum_sq_deg). Rewrite variance as the sum over nonempty $S$ of $\widehat f(S)^2$ (BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier), and distribute the factor $k$ across that sum. Compare summands. For $S=\varnothing$, both contributions are zero. For nonempty $S$ with $\widehat f(S)=0$, both are again zero. Otherwise, the degree hypothesis gives $|S|\le k$; multiplying by the nonnegative square $\widehat f(S)^2$ yields the required summand inequality. Summing over all $S$ proves the bound.

**Key facts.** `BooleanAnalysis.totalInfluence_eq_sum_sq_deg`, `BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier`.
