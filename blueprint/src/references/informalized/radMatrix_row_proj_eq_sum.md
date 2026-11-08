<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: radMatrix_row_proj_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula for a Scaled Row Projection

**Claim.** The $i$th coordinate of the image of $x$ under the scaled matrix is the sum over columns of $(x_j/\sqrt{k})\omega_{ij}$.

**Proof.** By the definition of the matrix action, the coordinate is $\sum_j (\omega_{ij}/\sqrt{k})x_j$. For each summand, commutativity and associativity of multiplication give $(\omega_{ij}/\sqrt{k})x_j=(x_j/\sqrt{k})\omega_{ij}$. Replacing each term in the finite sum yields the stated formula.
