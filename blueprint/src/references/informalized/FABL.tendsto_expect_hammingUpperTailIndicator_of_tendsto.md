<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_expect_hammingUpperTailIndicator_of_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Limit for Moving Thresholds

**Claim.** If $d(q)\to\infty$ and $u(q)\to a$, then the expected indicator that the normalized Rademacher sum in dimension $d(q)$ exceeds $u(q)$ converges to the standard Gaussian upper tail at $a$.

**Proof.** Bound the error from the desired limit by the sum of the error from the expectation to the Gaussian upper tail at $u(q)$ and the change in Gaussian upper tail from $u(q)$ to $a$. Eventually $d(q)\ge1$, and the Berry–Esseen estimate (`abs_expect_hammingUpperTailIndicator_dimension_le`) bounds the first error by $2C(\sqrt{d(q)})^{-1}$, which tends to zero as $d(q)\to\infty$. The standard Gaussian upper tail is continuous (`continuous_standardGaussianUpperTail`), so $u(q)\to a$ makes the second error tend to zero. The sum tends to zero, yielding the claimed convergence.

**Key facts.** `FABL.abs_expect_hammingUpperTailIndicator_dimension_le`, `FABL.continuous_standardGaussianUpperTail`.
