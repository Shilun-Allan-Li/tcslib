<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.gaussianBivariateStability_one_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full Right Threshold

**Claim.** For all real $\rho$ and $0\le\alpha\le1$, one has $B_\rho(\alpha,1)=\alpha$.

**Proof.** The condition that the transformed coordinate have CDF at most one always holds, since the Gaussian CDF is strictly less than one everywhere. Thus the defining event reduces to the condition $\Phi(x)\le\alpha$. The first-coordinate projection preserves the standard Gaussian law under product Gaussian measure, so this event has measure $\alpha$ for $\alpha\in[0,1]$ (\texttt{BooleanAnalysis.GaussianSpace.measureReal_standardGaussianCDF_comp_le}).

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_lt_one`, `BooleanAnalysis.GaussianSpace.measureReal_standardGaussianCDF_comp_le`.
