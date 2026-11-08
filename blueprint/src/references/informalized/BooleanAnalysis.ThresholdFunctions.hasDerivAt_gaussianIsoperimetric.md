<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.hasDerivAt_gaussianIsoperimetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Gaussian profile

**Claim.** At each $a\in(0,1)$, the Gaussian profile is differentiable with derivative $U'(a)=-Q(a)$.

**Proof.** Apply the chain rule to the Gaussian density evaluated at the quantile. The density has derivative $-x\varphi(x)$ at $x$ (`hasDerivAt_standardGaussianPDF`), while the quantile has derivative $1/U(a)$ at $a$ (`hasDerivAt_standardGaussianQuantile`). At $x=Q(a)$, the density is $U(a)$; multiplying the two derivatives gives $-Q(a)U(a)/U(a)=-Q(a)$. The cancellation is valid because the Gaussian density is positive (`standardGaussianPDF_pos`).

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianPDF`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianQuantile`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
