<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Gaussian CDF

**Claim.** For every real $t$, the standard Gaussian distribution function satisfies $0<\Phi(t)$.

**Proof.** A CDF is nonnegative at $t-1$. Since $t-1<t$, strict monotonicity of the standard Gaussian CDF gives $\Phi(t-1)<\Phi(t)$. Together these imply $0<\Phi(t)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_strictMono`.
