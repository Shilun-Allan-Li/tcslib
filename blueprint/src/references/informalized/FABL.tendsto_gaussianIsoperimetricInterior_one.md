<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.tendsto_gaussianIsoperimetricInterior_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian isoperimetric interior near one

**Claim.** As $\alpha$ tends to $1$ from below, the standard Gaussian density at the upper quantile corresponding to tail probability $\alpha$ tends to $0$.

**Proof.** The upper quantile tends to negative infinity as the tail probability approaches $1$ from below, by `tendsto_standardGaussianUpperQuantileReal_one`. The standard Gaussian density tends to zero at negative infinity, by `tendsto_standardGaussianDensity_atBot`. Composing these two limits shows that the density evaluated at the upper quantile tends to zero, which is the asserted interior limit.

**Key facts.** `FABL.tendsto_standardGaussianDensity_atBot`, `FABL.tendsto_standardGaussianUpperQuantileReal_one`.
