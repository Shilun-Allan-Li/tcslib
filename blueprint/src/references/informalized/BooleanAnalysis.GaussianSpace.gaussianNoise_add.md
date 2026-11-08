<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Gaussian Noise

**Claim.** For integrable $f$ and $g$ and $\rho\in[-1,1]$, the Gaussian noise operator sends their pointwise sum to the sum of their noise images, pointwise.

**Proof.** Fix an input point $x$. The integrands defining the noise images of $f$ and $g$ are integrable under the Gaussian measure, by the integrability of each function and the fact that the Gaussian endpoint transformation preserves that measure ($\texttt{integrable_gaussianNoise_integrand}$). Linearity of the integral then says that the integral of the sum of these integrands is the sum of their integrals. Since this holds for each $x$, the two resulting functions agree pointwise.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_gaussianNoise_integrand`.
