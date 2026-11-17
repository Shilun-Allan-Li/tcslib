<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdMoments.lean :: BooleanAnalysis.GaussianSpace.Invariance.affine_abs_third_moment_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third moment bound for affine transforms

**Claim.** Under the stated hypercontractivity, mean, and second-moment assumptions, the third absolute moment of $a+bX$ is at most $\bigl(a^2+(b/\rho)^2\bigr)^{3/2}$.

**Proof.** The affine function $Z=a+bX$ belongs to $L^3$: constants belong to $L^3$ on a probability space, and the assumed $L^3$ integrability of $X$ is preserved by scalar multiplication and addition. The affine three-norm estimate for a hypercontractive random variable, using the zero mean and unit second moment, gives $\|Z\|_3^2\le B$, where $B=a^2+(b/\rho)^2$. The third-moment estimate from the three-norm bound then gives $\int |Z|^3\,d\mu\le B^{3/2}$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.IsHypercontractive.affine_three_norm_sq`, `BooleanAnalysis.GaussianSpace.Invariance.third_moment_le_of_three_norm_sq`.
