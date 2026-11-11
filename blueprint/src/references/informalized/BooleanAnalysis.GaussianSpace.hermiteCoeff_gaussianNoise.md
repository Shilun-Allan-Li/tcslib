<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Noise.lean :: BooleanAnalysis.GaussianSpace.hermiteCoeff_gaussianNoise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Coefficients Under Gaussian Noise

**Claim.** For square-integrable $f$ and correlation parameter $\rho\in[-1,1]$, Gaussian noise multiplies the Hermite coefficient at $\alpha$ by $\rho^{|\alpha|}$, where $|\alpha|=\sum_i\alpha_i$.

**Proof.** The Hermite coefficient is the Gaussian integral of a function against the Hermite function. Apply self-adjointness of Gaussian noise (`gaussianNoise_selfAdjoint`) to move the noise operator from $f$ onto the Hermite function; the required square-integrability holds for $f$ by hypothesis and for the Hermite function by `hermiteFunction_memLp_two`. The noise action on a Hermite function is diagonal: it sends $H_\alpha$ to $\rho^{|\alpha|}H_\alpha$ (`gaussianNoise_hermiteFunction`). Pulling this constant out of the integral leaves $\rho^{|\alpha|}$ times the coefficient of $f$, as claimed.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteFunction_memLp_two`, `BooleanAnalysis.GaussianSpace.gaussianNoise_selfAdjoint`, `BooleanAnalysis.GaussianSpace.gaussianNoise_hermiteFunction`.
