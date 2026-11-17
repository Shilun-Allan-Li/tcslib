<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.measureReal_standardGaussianCDF_comp_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity of the Gaussian CDF transform

**Claim.** If $X$ pushes $\mu$ forward to the standard Gaussian measure, then for each $a\in[0,1]$, the real measure of $\{\omega:\Phi(X(\omega))\le a\}$ equals $a$.

**Proof.** Because $X$ is measure-preserving, the measure of the preimage of the CDF sublevel set equals the standard Gaussian measure of that set; continuity of $\Phi$ ensures the set is measurable. The Gaussian CDF sublevel measure is $a$ (`measureReal_standardGaussianCDF_le`), giving the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.measureReal_standardGaussianCDF_le`, `BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianCDF`.
