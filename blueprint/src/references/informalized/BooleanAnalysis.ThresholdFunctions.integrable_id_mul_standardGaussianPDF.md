<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.integrable_id_mul_standardGaussianPDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian first-moment integrability

**Claim.** The function $x\mapsto x\varphi(x)$ is integrable over the real line.

**Proof.** The Gaussian density is a constant multiple of $e^{-x^2/2}$, so $x\varphi(x)$ is the same constant multiple of $x e^{-x^2/2}$. The standard Gaussian integrability result for a linear factor times a decaying quadratic exponential gives integrability of this function; multiplying an integrable function by a constant preserves integrability.
