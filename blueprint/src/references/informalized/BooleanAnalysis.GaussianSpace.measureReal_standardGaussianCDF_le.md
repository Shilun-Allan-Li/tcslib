<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.measureReal_standardGaussianCDF_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian CDF sublevel measure

**Claim.** For every $a\in[0,1]$, the standard Gaussian measure of $\{t:\Phi(t)\le a\}$ is $a$.

**Proof.** At $a=0$, the sublevel set is empty because $\Phi(t)>0$ for every real $t$ (`standardGaussianCDF_pos`), so its measure is zero. At $a=1$, the set is all of $\mathbb R$ because $\Phi(t)<1$ everywhere (`standardGaussianCDF_lt_one`), so its probability measure is one. In the remaining case $0<a<1$, strict monotonicity of $\Phi$ and the quantile identity $\Phi(\Phi^{-1}(a))=a$ (`standardGaussianCDF_quantile`) identify the sublevel set with $(-\infty,\Phi^{-1}(a)]$. The measure of this half-line is its CDF value, hence $a$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_lt_one`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_quantile`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_strictMono`.
