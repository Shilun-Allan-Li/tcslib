<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.tendsto_integral_abs_averagedGaussianIndicator_sub_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence of averaged indicators

**Claim.** For a measurable set $A\subseteq\mathbb R^n$, the integral of the absolute difference between its averaged Gaussian indicator at angle $\theta$ and its indicator tends to zero as $\theta\to0$.

**Proof.** For each angle, the integral in question equals the rotation sensitivity of $A$ (integral_abs_averagedGaussianIndicator_sub_indicator). The rotation sensitivity tends to zero at the origin for measurable $A$ (rotationSensitivity_tendsto_zero). Substitution gives the claimed limit.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_abs_averagedGaussianIndicator_sub_indicator`, `BooleanAnalysis.GaussianSpace.rotationSensitivity_tendsto_zero`.
