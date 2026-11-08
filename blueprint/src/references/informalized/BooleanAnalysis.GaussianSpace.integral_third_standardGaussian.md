<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InputMoments.lean :: BooleanAnalysis.GaussianSpace.integral_third_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Third Gaussian Moment

**Claim.** The third moment of the standard Gaussian measure on $\mathbb R$ is zero.

**Proof.** The standard Gaussian measure is invariant under reflection $x\mapsto -x$, by the reflection invariance of a centered Gaussian law. Changing variables by this measure-preserving reflection shows that the integral of $x^3$ equals the integral of $(-x)^3=-x^3$. Hence the integral equals its own negative and must be zero.
