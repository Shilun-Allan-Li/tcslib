<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.abs_measureReal_standardGaussianCDF_inter_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian CDF Threshold Measure Stability

**Claim.** For thresholds $a,b\in[0,1]$, the absolute difference between the measures of the two threshold events intersected with $A$ is at most $|a-b|$.

**Proof.** It suffices to treat $a\le b$: if the order is reversed, exchange the thresholds, which leaves both absolute values unchanged. Under $a\le b$, the event with threshold $a$ is contained in the event with threshold $b$, so their intersections with $A$ have ordered measures. The one-sided estimate for the difference of these measures is the Gaussian CDF threshold bound (`measureReal_standardGaussianCDF_inter_sub_le`). Since both differences have the same sign, this one-sided estimate is precisely the desired absolute-value bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.measureReal_standardGaussianCDF_inter_sub_le`.
