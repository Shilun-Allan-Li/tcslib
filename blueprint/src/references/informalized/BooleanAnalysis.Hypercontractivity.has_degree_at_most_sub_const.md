<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.has_degree_at_most_sub_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subtracting a Constant Preserves Degree

**Claim.** If a Boolean function has Fourier degree at most $k$, then subtracting any constant from it preserves that degree bound.

**Proof.** Fix a set of coordinates $S$. If $S$ is empty, its cardinality is zero, so it is already at most $k$. If $S$ is nonempty, the Fourier coefficient of the constant function at $S$ vanishes: the empty character has inner product zero with the character indexed by $S$, by character orthogonality (`fourier_coeff_chi`) and the fact that the empty character is constantly one (`chiS_empty`). By linearity of expectation (`expect_sub` and `expect_const_mul`), the coefficient of $f-c$ at $S$ therefore equals the coefficient of $f$ at $S$. Whenever the former is nonzero, so is the latter, and the assumed degree bound for $f$ gives $|S|\le k$.

**Key facts.** `BooleanAnalysis.chiS_empty`, `BooleanAnalysis.fourier_coeff_chi`, `BooleanAnalysis.ThresholdFunctions.expect_sub`, `BooleanAnalysis.ThresholdFunctions.expect_const_mul`.
