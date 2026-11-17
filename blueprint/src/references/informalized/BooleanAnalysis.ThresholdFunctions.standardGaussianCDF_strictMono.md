<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_strictMono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Increase of the Gaussian CDF

**Claim.** The standard Gaussian distribution function $\Phi$ is strictly increasing: if $a<b$, then $\Phi(a)<\Phi(b)$.

**Proof.** At each real $x$, the derivative of $\Phi$ is the standard Gaussian density $\varphi(x)$, by the derivative formula for the Gaussian CDF (`hasDerivAt_standardGaussianCDF`). This derivative is positive everywhere (`standardGaussianPDF_pos`). The mean value theorem therefore implies that $\Phi$ is strictly increasing.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
