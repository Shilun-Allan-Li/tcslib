<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂LearningSampleCount_budget_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Learning Sample Count Budget

**Claim.** For every $n,\ell\in\mathbb{N}$ and rational learning parameter $\delta$ with $0<\delta\leq\frac12$, if $M$ is the sample count, then $2^{D}\exp(-M2^{-\ell})\leq\delta$, where $D$ is the number of subsets of $[n]$ of size at most $\ell$.

**Proof.** Write $D$ for the number of allowed monomials and $b$ for the number of failure bits. First, $e^{-1}\leq 1/2$; raising both sides to the nonnegative integer power $D+b$ gives $e^{-(D+b)}\leq 2^{-(D+b)}$. Next, the failure-bit bound gives $2/2^b\leq\delta$, hence $2^{-b}\leq\delta$ as well. The scaled-sample-count identity shows that $M2^{-\ell}=D+b$, so the target expression equals $2^D e^{-(D+b)}$. By the exponential estimate this is at most $2^D2^{-(D+b)}=2^{-b}$, which is at most $\delta$.

**Key facts.** `FABL.lowDegreeF₂LearningSampleCount_mul_invTwoPow`, `FABL.two_div_pow_fourierEstimatorFailureBits_le`.
