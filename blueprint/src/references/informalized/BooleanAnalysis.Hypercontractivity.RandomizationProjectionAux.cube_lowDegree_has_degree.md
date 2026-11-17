<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.cube_lowDegree_has_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a Fourier truncation

**Claim.** Every nonzero Fourier–Walsh coefficient of the Fourier truncation to sets of size at most $k$ is indexed by a set of size at most $k$.

**Proof.** Take any set $S$ whose coefficient in the truncation is nonzero. If $|S|>k$, the coefficient formula (`KKL.fourierCoeff_lowDegreePart`) identifies that coefficient with zero, contradicting the choice of $S$. Hence $|S|\le k$, as required.

**Key facts.** `KKL.fourierCoeff_lowDegreePart`.
