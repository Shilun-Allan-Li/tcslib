<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.norm_sum_sum_coordinateTensor_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate tensor sum norm bound

**Claim.** For real coefficients $a_{ij}$, the operator norm of the coordinate tensor sum is at most $\sum_{i,j}|a_{ij}|$.

**Proof.** Apply the triangle inequality first to the outer sum over $i$ and then to each inner sum over $j$. Each resulting term is a scalar multiple of a rank-one operator formed from two coordinate projections. The norm of such a tensor operator is the product of the norms of those projections; each is at most $1$ (`norm_coordinateProjection_le_one`). Consequently the term indexed by $(i,j)$ has norm at most $|a_{ij}|$. Summing these bounds proves the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.norm_coordinateProjection_le_one`.
