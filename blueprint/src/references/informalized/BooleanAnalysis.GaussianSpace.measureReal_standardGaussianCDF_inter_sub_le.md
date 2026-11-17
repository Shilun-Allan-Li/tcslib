<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.measureReal_standardGaussianCDF_inter_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian CDF band measure bound

**Claim.** For a finite measure space and a measure-preserving map $X$ to the standard Gaussian measure, if $A$ is measurable and $a,b\in[0,1]$ with $a\le b$, then the difference of the measures of $A\cap\{\Phi(X)\le b\}$ and $A\cap\{\Phi(X)\le a\}$ is at most $b-a$.

**Proof.** The sublevel set at $a$ is contained in the one at $b$. For nested measurable sets, the difference of the measures of their intersections with $A$ is at most the measure of their set difference. That difference is contained in the full CDF band $\{\Phi(X)\le b\}\setminus\{\Phi(X)\le a\}$. Its measure is exactly $b-a$: each sublevel set has measure equal to its threshold by uniformity of the Gaussian CDF transform (`measureReal_standardGaussianCDF_comp_le`), and subtracting these measures computes the measure of the difference. Continuity of the CDF ensures the sublevel sets are measurable.

**Key facts.** `BooleanAnalysis.GaussianSpace.measureReal_standardGaussianCDF_comp_le`, `BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianCDF`.
