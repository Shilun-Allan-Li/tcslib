<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Gaussian Distribution Function

**Claim.** For every real $t$, the standard Gaussian distribution function $\Phi$ is differentiable at $t$ with derivative $\varphi(t)$.

**Proof.** For each $b$, the increment of the distribution function from $0$ to $b$ is the integral of its density: $\Phi(b)-\Phi(0)=\int_0^b\varphi(x)\,dx$ (\texttt{standardGaussianCDF_sub}). Since the density is continuous (\texttt{continuous_standardGaussianPDF}), the fundamental theorem of calculus gives derivative $\varphi(t)$ for this integral as a function of its upper endpoint. Adding the constant $\Phi(0)$ does not change the derivative, proving the claim.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_sub`, `BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianPDF`.
