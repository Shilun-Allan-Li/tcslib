<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Kernel.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussianNoise_compose_integrand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Composed Gaussian Noise Integrand

**Claim.** If $f$ is integrable under the product standard Gaussian measure and $\rho,\sigma\in[-1,1]$, then the stated three-variable Gaussian noise composition of $f$ is integrable under the product law of three independent standard Gaussian vectors.

**Proof.** First regroup the three independent vectors as a pair consisting of $(x,y)$ and $z$; the product-association map preserves the product measure. The Gaussian endpoint map with parameter $\rho$ sends $(x,y)$ to $\rho x+\sqrt{1-\rho^2}\,y$ and preserves standard Gaussian measure. Pairing this map with the identity on $z$ preserves the corresponding product measure. Applying the Gaussian endpoint map with parameter $\sigma$ to the resulting pair again preserves standard Gaussian measure. The composition of these measure-preserving maps is measure-preserving, and its first output is exactly the argument of $f$ in the claim. Pulling back an integrable function along a measure-preserving map preserves integrability, yielding the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianEndpoint`.
