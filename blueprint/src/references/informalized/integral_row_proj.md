<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: integral_row_proj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a row projection

**Claim.** For a fixed vector and row, the corresponding coordinate of the scaled Rademacher matrix image has expectation zero.

**Proof.** The row projection is the finite sum over coordinates $j$ of $(x_j/\sqrt{k})\omega_{ij}$ (`radMatrix_row_proj_eq_sum`). Each summand is integrable, as follows from its $L^2$ bound (`memLp_scaled_entry`). Linearity of integration therefore reduces the expectation to the sum of the expectations of these terms. Pulling out the deterministic coefficient leaves the mean of the entry $\omega_{ij}$, which is zero (`integral_entry`). Every summand vanishes, so the row projection has mean zero.

**Key facts.** `radMatrix_row_proj_eq_sum`, `memLp_scaled_entry`, `integral_entry`.
