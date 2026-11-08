<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.measurable_gaussianBivariateStability_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of Composed Gaussian Stability

**Claim.** Composing Gaussian bivariate stability with measurable functions valued in $[0,1]$ gives a measurable function when the correlation lies in $[-1,1]$.

**Proof.** The pair map $x\mapsto(f(x),g(x))$ is measurable, and the range conditions place it in $[0,1]\times[0,1]$. For the fixed correlation $\rho\in[-1,1]$, Gaussian bivariate stability is continuous on this square by the continuity theorem for that function (BooleanAnalysis.GaussianSpace.continuousOn_gaussianBivariateStability). Its restriction to the square is therefore measurable. Composing this measurable restriction with the measurable pair map proves the assertion.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuousOn_gaussianBivariateStability`.
