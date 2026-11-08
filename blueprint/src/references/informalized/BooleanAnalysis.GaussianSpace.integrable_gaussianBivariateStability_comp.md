<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussianBivariateStability_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of Composed Gaussian Bivariate Stability

**Claim.** For a finite measure space, $\rho\in[-1,1]$, and measurable $[0,1]$-valued functions $f,g$, the composed Gaussian bivariate stability function is integrable.

**Proof.** The composition is measurable by `measurable_gaussianBivariateStability_comp`. For every pair of arguments, Gaussian bivariate stability lies in $[0,1]$ (`gaussianBivariateStability_mem_unitInterval`), so the composed function is nonnegative and bounded above by $1$. A measurable bounded function is integrable on a finite measure space.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurable_gaussianBivariateStability_comp`, `BooleanAnalysis.GaussianSpace.gaussianBivariateStability_mem_unitInterval`.
