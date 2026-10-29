<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean :: BooleanAnalysis.Hypercontractivity.expect_sq_noiseOp_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# The expected square of a smoothed Boolean function is nonnegative

**Claim.** Let $f\colon\{0,1\}^n\to\mathbb R$ be a Boolean function and $\rho\in\mathbb R$ arbitrary. Form the noise-operator image $T_\rho f$ and average its square over the uniform measure on the cube. The resulting quantity $\mathbb E\!\left[(T_\rho f)^2\right]$ is nonnegative.

**Proof.** The claim is proved by unwinding the definition of the uniform average and observing that it exhibits the quantity as a product of two manifestly nonnegative factors.
