<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.tendsto_expect_hammingUpperTailIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Tail Limit

**Claim.** For fixed $t\in\mathbb R$, the expected indicator that the normalized Rademacher sum in dimension $m+1$ exceeds $t$ converges to the standard Gaussian upper tail at $t$.

**Proof.** By the Berry–Esseen estimate for this tail probability (`abs_expect_hammingUpperTailIndicator_sub_standardGaussianUpperTail`), the absolute difference between the expectation and the Gaussian upper tail is at most $2C$ times the normalized Rademacher coefficient in dimension $m+1$, where $C$ is the third-moment Berry–Esseen constant. The coefficient tends to zero (`tendsto_normalizedRademacherCoefficient_succ`), so this error tends to zero as well. The distance from the expectation to the Gaussian tail is nonnegative and bounded above by that error; the squeeze theorem therefore gives the claimed convergence.

**Key facts.** `FABL.abs_expect_hammingUpperTailIndicator_sub_standardGaussianUpperTail_le`, `FABL.tendsto_normalizedRademacherCoefficient_succ`.

**Caveat.** The informal statement also mentions convergence of the level-one Fourier weight; the formal declaration and proof establish only the expectation limit.
