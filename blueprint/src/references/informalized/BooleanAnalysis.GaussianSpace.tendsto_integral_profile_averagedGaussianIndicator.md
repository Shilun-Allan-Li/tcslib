<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProfileApproximation.lean :: BooleanAnalysis.GaussianSpace.tendsto_integral_profile_averagedGaussianIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Gaussian profile integral

**Claim.** For measurable $A\subseteq\mathbb R^n$, the integral of the closed Gaussian profile of its averaged indicator tends to zero as $\theta\to0$.

**Proof.** Use the order characterization of a real limit. The integral is nonnegative for every angle, because the closed Gaussian profile is nonnegative (closedGaussianProfile_nonneg); this proves the required eventual lower bounds. For an arbitrary upper threshold $b>0$, the profile integral estimate (integral_profile_averagedGaussianIndicator_le), applied with $\varepsilon=b/2$, gives a constant $C>0$ such that the integral is at most $b/2+C$ times the rotation sensitivity, with the intended bound $b/2+C\,\mathrm{rotationSensitivity}(A,\theta)$. The rotation sensitivity tends to zero (rotationSensitivity_tendsto_zero), so this upper bound tends to $b/2<b$. Consequently the integral is eventually below $b$. The lower and upper bounds establish convergence to zero.

**Key facts.** `BooleanAnalysis.GaussianSpace.closedGaussianProfile_nonneg`, `BooleanAnalysis.GaussianSpace.integral_profile_averagedGaussianIndicator_le`, `BooleanAnalysis.GaussianSpace.rotationSensitivity_tendsto_zero`.
