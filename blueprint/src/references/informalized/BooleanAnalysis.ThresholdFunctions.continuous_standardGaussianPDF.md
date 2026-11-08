<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianPDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian density

**Claim.** The standard Gaussian density $\varphi(x)=e^{-x^2/2}/\sqrt{2\pi}$ is continuous on $\mathbb R$.

**Proof.** Rewrite the density as the constant $(\sqrt{2\pi})^{-1}$ times $\exp(-x^2/2)$, using the stated formula for the standard Gaussian density (standardGaussianPDF_eq). The polynomial $-x^2/2$ is continuous, as is the exponential function, and multiplying by a constant preserves continuity. Thus the density is continuous.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`.
