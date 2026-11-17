<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂LearningSampleCount_mul_invTwoPow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaled Learning Sample Count Identity

**Claim.** For every $n,\ell\in\mathbb{N}$ and rational learning parameter $\delta$ with $0<\delta\leq\frac12$, the learning sample count multiplied by $2^{-\ell}$ equals the monomial count plus the number of failure bits.

**Proof.** Expand the sample count as $2^\ell(D+b)$, where $D$ is the monomial count and $b$ is the failure-bit count. After casting to the reals, multiply by $(2^{-1})^\ell=2^{-\ell}$. The powers of $2$ cancel, leaving $D+b$.
