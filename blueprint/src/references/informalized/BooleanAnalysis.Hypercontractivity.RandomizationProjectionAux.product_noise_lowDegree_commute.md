<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.product_noise_lowDegree_commute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise commutes with low degree projection

**Claim.** Applying the noise operator to the low degree projection gives the same result as applying the low degree projection after the noise operator.

**Proof.** Evaluate both functions at an arbitrary point and expand the noise operator as a sum over sets $S$. The component of the low degree projection on $S$ is the original component when $|S|\le k$ and zero otherwise (`BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.component_lowDegree`). Meanwhile, the component of the noise-smoothed function is the original component multiplied by $\rho^{|S|}$ (`BooleanAnalysis.Hypercontractivity.RandomizationAux.component_noise`). In both expressions, the term indexed by $S$ is therefore $\rho^{|S|}$ times the original component when $|S|\le k$, and zero otherwise. The sums agree at every point, hence the functions are equal.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.component_lowDegree`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_noise`.
