<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.gaussianIsoperimetric_le_of_le_of_add_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Gaussian profile

**Claim.** If $a,b\in(0,1)$, $a\le b$, and $a+b\le1$, then $U(a)\le U(b)$.

**Proof.** Write the profile using the Gaussian density formula: $U(\alpha)=(2\pi)^{-1/2}\exp(-Q(\alpha)^2/2)$ (`standardGaussianPDF_eq`). The quantile square comparison gives $Q(b)^2\le Q(a)^2$ under the stated hypotheses (`standardGaussianQuantile_sq_le`). Negating and dividing by $2$ reverses this comparison, so $-Q(a)^2/2\le -Q(b)^2/2$. Since the exponential is increasing, the exponential factor at $a$ is at most the one at $b$. The common prefactor is positive, yielding $U(a)\le U(b)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`, `BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_sq_le`.
