<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: variance_row_proj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Row Projection

**Claim.** For $k>0$, the variance of the $i$-th coordinate of the image of $x$ under the random scaled matrix is $\|x\|^2/k$.

**Proof.** 1. The row projection is the sum over coordinates $j$ of the random variables $(x_j/\sqrt{k})\omega_{ij}$ (radMatrix_row_proj_eq_sum).
2. These summands are square-integrable (memLp_scaled_entry) and independent across $j$, by independence of the entries in a row (radMatrix_scaled_row_iid). Variance of a sum of independent square-integrable random variables is the sum of their variances.
3. Each summand has variance $x_j^2/k$ (variance_scaled_entry). Summing gives $\sum_j x_j^2/k$, which equals $\|x\|^2/k$ by the coordinate formula for the Euclidean norm (norm_sq_div_eq_sum).

**Key facts.** `radMatrix_row_proj_eq_sum`, `memLp_scaled_entry`, `radMatrix_scaled_row_iid`, `variance_scaled_entry`, `norm_sq_div_eq_sum`.
