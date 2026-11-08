<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂LearningSampleCount_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for Learning Sample Count

**Claim.** For every $n,\ell\in\mathbb{N}$ and every rational learning parameter $\delta$ with $0<\delta\leq\frac12$, the learning sample count is at most $2^\ell\big((\ell+1)(n+1)^\ell+\lceil\log_2\lceil2/\delta\rceil\rceil\big)$.

**Proof.** By definition, the sample count is $2^\ell$ times the sum of the monomial count and the failure-bit count. The monomial-count bound replaces the first summand by $(\ell+1)(n+1)^\ell$. Adding the unchanged failure-bit count preserves the inequality, and multiplication by the nonnegative factor $2^\ell$ gives the claimed bound.

**Key facts.** `FABL.lowDegreeF₂MonomialCount_le`.
