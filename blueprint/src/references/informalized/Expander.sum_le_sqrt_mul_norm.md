<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.sum_le_sqrt_mul_norm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate sum bounded by the Euclidean norm

**Claim.** For every Euclidean vector $x$, its coordinate sum satisfies $\sum_j x_j\le\sqrt{n}\,\|x\|$.

**Proof.** Cauchy–Schwarz applied to the constant vector with all coordinates one gives $(\sum_j x_j)^2\le n\sum_j x_j^2$. Therefore $\sum_j x_j\le|\sum_j x_j|\le\sqrt{n\sum_j x_j^2}$. The sum of the squared coordinates is $\|x\|^2$, so the right-hand side is $\sqrt{n}\,\|x\|$.
