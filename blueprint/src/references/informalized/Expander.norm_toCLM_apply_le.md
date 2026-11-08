<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.norm_toCLM_apply_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Contraction of a symmetric stochastic matrix

**Claim.** If $A$ is symmetric, has nonnegative entries, and each row sums to one, then $\|Av\|\le \|v\|$ for every vector $v$.

**Proof.** Symmetry and the row-sum condition imply that every column also sums to one. For each row $i$, apply the weighted Cauchy–Schwarz inequality with weights $A_{ij}$: nonnegativity and the fact that these weights sum to one give $(\sum_j A_{ij}v_j)^2\le \sum_j A_{ij}v_j^2$. Sum over $i$ and exchange the order of summation. The column sums reduce the result to $\sum_j v_j^2$. These two sums are the squared Euclidean norms of $Av$ and $v$, respectively; taking square roots proves the claim.
