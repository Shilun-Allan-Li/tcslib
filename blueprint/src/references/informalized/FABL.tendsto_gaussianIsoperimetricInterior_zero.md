<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.tendsto_gaussianIsoperimetricInterior_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian isoperimetric interior near zero

**Claim.** As $\alpha$ tends to $0$ from above, the standard Gaussian density at the corresponding upper quantile tends to $0$.

**Proof.** The upper quantile tends to positive infinity as its tail probability tends to zero from above, by `tendsto_standardGaussianUpperQuantileReal_zero`. The standard Gaussian density tends to zero at positive infinity, by `tendsto_standardGaussianDensity_atTop`. Composing these limits gives the claimed convergence of the density evaluated at the upper quantile.

**Key facts.** `FABL.tendsto_standardGaussianDensity_atTop`, `FABL.tendsto_standardGaussianUpperQuantileReal_zero`.
