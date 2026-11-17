<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.lipschitzOnWith_gaussianBivariateStability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz continuity of bivariate stability

**Claim.** For $\rho\in[-1,1]$, Gaussian bivariate stability on $[0,1]^2$ is Lipschitz with constant $2$ for the product metric.

**Proof.** Take two points $p=(\alpha,\beta)$ and $q=(\alpha',\beta')$ in the square. The stability difference estimate (`abs_gaussianBivariateStability_sub_le`) bounds the absolute difference of their values by $|\alpha-\alpha'|+|\beta-\beta'|$. In the product metric, each coordinate distance is at most the maximum of the two coordinate distances, so this sum is at most $2\,\mathrm{dist}(p,q)$. This is precisely the claimed Lipschitz bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_gaussianBivariateStability_sub_le`.
