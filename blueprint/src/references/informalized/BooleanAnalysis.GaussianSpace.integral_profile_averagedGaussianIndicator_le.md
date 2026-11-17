<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProfileApproximation.lean :: BooleanAnalysis.GaussianSpace.integral_profile_averagedGaussianIndicator_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Profile Bound by Rotation Sensitivity

**Claim.** For every measurable set and every positive tolerance, there is a positive constant such that the integrated closed Gaussian profile of the averaged Gaussian indicator is bounded by that tolerance plus the constant times the rotation sensitivity.

**Proof.** Choose a positive constant $C$ from the endpoint estimate for the closed Gaussian profile (`closedGaussianProfile_endpoint_bound`): whenever $p\in[0,1]$ and $b$ is either $0$ or $1$, the profile at $p$ is at most $\varepsilon+C|p-b|$. For each $x$, the averaged Gaussian indicator lies in $[0,1]$ (`averagedGaussianIndicator_mem_unitInterval`), and the indicator of the set at $x$ is either zero or one. Apply the endpoint estimate with these values. The profile is nonnegative (`closedGaussianProfile_nonneg`), and the pointwise bound can therefore be integrated. The absolute difference between the averaged indicator and the set indicator is integrable: the averaged indicator is integrable (`integrable_averagedGaussianIndicator`), the measurable set indicator is integrable under the probability measure, and their difference is integrable. Finally, the integral of this absolute difference equals the rotation sensitivity (`integral_abs_averagedGaussianIndicator_sub_indicator`). Linearity and the fact that the measure is a probability measure yield the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.closedGaussianProfile_endpoint_bound`, `BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_mem_unitInterval`, `BooleanAnalysis.GaussianSpace.closedGaussianProfile_nonneg`, `BooleanAnalysis.GaussianSpace.integrable_averagedGaussianIndicator`, `BooleanAnalysis.GaussianSpace.integral_abs_averagedGaussianIndicator_sub_indicator`.
