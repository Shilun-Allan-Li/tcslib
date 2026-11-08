<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: integral_sq_row_proj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second moment of a row projection

**Claim.** For a fixed vector and row of the scaled Rademacher matrix, the second moment of the row projection is $\|x\|^2/k$.

**Proof.** First, the row projection belongs to $L^2$: express it as a finite sum of scaled entries using `radMatrix_row_proj_eq_sum`, and apply the $L^2$ bound for each summand (`memLp_scaled_entry`). The variance identity for an $L^2$ random variable says its second moment is its variance plus the square of its mean. The variance of this row projection is $\|x\|^2/k$ (`variance_row_proj`), while its mean is zero (`integral_row_proj`). Substitution gives the claimed second moment.

**Key facts.** `radMatrix_row_proj_eq_sum`, `memLp_scaled_entry`, `variance_row_proj`, `integral_row_proj`.
