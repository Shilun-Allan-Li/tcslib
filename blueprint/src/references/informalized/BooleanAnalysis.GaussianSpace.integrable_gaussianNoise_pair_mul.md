<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Kernel.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussianNoise_pair_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Gaussian noise pair product

**Claim.** If $f$ and $g$ belong to $L^2(\gamma_n)$ and $\rho\in[-1,1]$, then $(x,y)\mapsto f(x)g(\rho x+\sqrt{1-\rho^2}\,y)$ is integrable under $\gamma_n\otimes\gamma_n$.

**Proof.** On the product probability space, the first-coordinate projection has law $\gamma_n$, so composing $f$ with that projection preserves its $L^2$ membership. The noise map $(x,y)\mapsto\rho x+\sqrt{1-\rho^2}\,y$ also has law $\gamma_n$ under the product measure, by the Gaussian endpoint measure-preservation fact (`measurePreserving_gaussianEndpoint`); consequently, composing $g$ with this map preserves its $L^2$ membership. The product of two $L^2$ functions on the same measure space is integrable by the Cauchy–Schwarz inequality, giving the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianEndpoint`.
