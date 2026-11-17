<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Indicator.lean :: BooleanAnalysis.GaussianSpace.gaussianNoiseStability_indicator_measure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator stability as a joint event

**Claim.** For measurable $A\subseteq\mathbb R^n$ and $\rho\in[-1,1]$, the Gaussian noise stability of the indicator of $A$ equals the correlated Gaussian measure of $A\times A$.

**Proof.** Use the correlated-integral identity to express the stability integral as the expectation of $1_A(z_1)1_A(z_2)$ under the correlated Gaussian measure; the indicator functions lie in $L^2$ because the underlying Gaussian law is a probability measure (\texttt{integral\_correlatedGaussianMeasure}). Since $A$ is measurable, $A\times A$ is measurable, and the product of the two indicators is exactly the indicator of this rectangle. Integrating that indicator gives the measure of $A\times A$, as claimed.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_correlatedGaussianMeasure`.
