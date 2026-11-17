<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell.lean :: BooleanAnalysis.GaussianSpace.gaussianHalfspaceStability_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability at zero correlation

**Claim.** For every $\alpha\in[0,1]$, Gaussian halfspace stability with correlation parameter $0$ and measure parameter $\alpha$ equals $\alpha^2$.

**Proof.** At the endpoints, the definition gives stability $0$ when $\alpha=0$ and $1$ when $\alpha=1$, which are the corresponding squares. For $0<\alpha<1$, the boundary branches are inactive. At correlation zero the event is the product of two copies of the half-line $(-\infty,q]$, where $q$ is the Gaussian quantile at $\alpha$. The product measure of this rectangle is the product of the two half-line measures. Each is the Gaussian CDF at $q$, and \texttt{standardGaussianCDF\_quantile} identifies that value with $\alpha$. The result is therefore $\alpha\cdot\alpha=\alpha^2$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_quantile`.
