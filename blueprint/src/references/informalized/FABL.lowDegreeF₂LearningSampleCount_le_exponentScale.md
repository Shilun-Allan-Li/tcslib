<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.lowDegreeF₂LearningSampleCount_le_exponentScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponent Scale for Learning Sample Count

**Claim.** For every $n,\ell\in\mathbb{N}$ and rational learning parameter $\delta$ with $0<\delta\leq\frac12$, the sample count is at most $2^\ell(\ell+\lceil\log_2\lceil2/\delta\rceil\rceil+1)(n+1)^\ell$.

**Proof.** Let $D$ be the monomial count, $b$ the failure-bit count, and $P=(n+1)^\ell$. The monomial-count bound gives $D\leq(\ell+1)P$. Since $P\geq1$, also $b\leq bP$. Adding these inequalities yields $D+b\leq((\ell+1)+b)P$. Multiplying by $2^\ell$ and collecting factors gives the stated sample-count bound.

**Key facts.** `FABL.lowDegreeF₂MonomialCount_le`.
