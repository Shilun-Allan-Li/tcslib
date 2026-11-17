<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell.lean :: BooleanAnalysis.GaussianSpace.gaussianHalfspaceStability_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability at full correlation

**Claim.** For every $\alpha\in[0,1]$, Gaussian halfspace stability with correlation parameter $1$ and measure parameter $\alpha$ equals $\alpha$.

**Proof.** If $\alpha=0$, the first branch in the definition gives stability $0$. If $\alpha=1$, the second branch gives stability $1$. In the remaining case $0<\alpha<1$, both branches are inactive. At correlation one the square-root coefficient vanishes and the event reduces to $z_1\le q$ and $z_1\le q$, where $q$ is the Gaussian quantile at $\alpha$; hence it is simply $z_1\le q$. The product measure of this set is the one-dimensional Gaussian measure of $(-\infty,q]$, since the other factor is the whole space and has measure one. By the relation between the Gaussian CDF and this half-line measure, this is the CDF at $q$. The quantile identity \texttt{standardGaussianCDF\_quantile} says that this CDF equals $\alpha$ for $0<\alpha<1$, proving the result in the interior as well.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_quantile`.
