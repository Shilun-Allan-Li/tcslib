<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.abs_projectOnCoordinates_le_productSupNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Projection Sup Norm Bound

**Claim.** For every input $x$, the absolute value of its coordinate projection is at most the supremum norm of $f$.

**Proof.** Let $M$ be the product supremum norm of $f$. At every point $y$, the defining supremum bound gives $|f(	ext{merge}(J,x,y))|\le M$, hence $-M\le f(\text{merge}(J,x,y))\le M$. Monotonicity of expectation carries both inequalities to the average over $y$. The expectation of either constant function $M$ or $-M$ is that same constant, so the projection lies between $-M$ and $M$, proving the result.

**Key facts.** `FABL.abs_le_productSupNorm`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_mono`.
