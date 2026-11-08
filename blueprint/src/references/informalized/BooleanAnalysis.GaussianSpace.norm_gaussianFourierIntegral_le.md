<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.norm_gaussianFourierIntegral_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Fourier integral norm bound

**Claim.** For a complex-valued function on $\mathbb R^n$, the norm of its Gaussian Fourier integral with the stated linear phase is at most the Gaussian integral of the function's norm.

**Proof.** The identity for the Gaussian Fourier integral (`gaussianFourierIntegral_eq`) rewrites the displayed integral as the Fourier integral of the function under the Gaussian measure, with the corresponding linear pairing. The general norm inequality for Fourier integrals bounds the norm of that Fourier integral by the integral of the norm of the integrand. This yields the claimed inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianFourierIntegral_eq`.
