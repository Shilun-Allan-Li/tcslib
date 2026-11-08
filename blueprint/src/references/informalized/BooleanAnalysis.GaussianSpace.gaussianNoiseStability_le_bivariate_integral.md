<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Interpolation.lean :: BooleanAnalysis.GaussianSpace.gaussianNoiseStability_le_bivariate_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Stability Bound

**Claim.** For measurable $f$ taking values in $[0,1]$ and $0<\rho<1$, its Gaussian noise stability is at most the expectation of the bivariate Gaussian stability at $(f(X),f(Y))$ under the correlated Gaussian measure.

**Proof.** Because $f$ is bounded, it belongs to Gaussian $L^2$. The correlated-measure integral formula ($\texttt{integral_correlatedGaussianMeasure}$) therefore identifies the noise stability with the integral of $f(z_1)f(z_2)$ over the correlated pair. For each pair $z=(z_1,z_2)$, the values $f(z_1),f(z_2)$ lie in $[0,1]$; the pointwise bound that their product is at most their bivariate Gaussian stability ($\texttt{mul_le_gaussianBivariateStability}$) applies. Both sides are integrable: the product by $\texttt{integrable_correlatedGaussianMeasure_mul}$ and the composed bivariate stability by $\texttt{integrable_gaussianBivariateStability_comp}$. Integrating the pointwise inequality gives the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_correlatedGaussianMeasure`, `BooleanAnalysis.GaussianSpace.integrable_correlatedGaussianMeasure_mul`, `BooleanAnalysis.GaussianSpace.integrable_gaussianBivariateStability_comp`, `BooleanAnalysis.GaussianSpace.mul_le_gaussianBivariateStability`.
