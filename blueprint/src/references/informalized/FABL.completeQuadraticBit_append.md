<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.completeQuadraticBit_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic bit of an appended vector

**Claim.** The complete quadratic bit of the vector formed by appending $y$ to $x$ equals the complete quadratic bit of $x$, plus that of $y$, plus $(\sum_i x_i)(\sum_j y_j)$.

**Proof.** Express each complete quadratic bit as a sum over all ordered pairs of coordinates, retaining a term only when the first coordinate is smaller than the second (FABL.completeQuadraticBit_eq_full_sum). Split the coordinates of the appended vector into those from $x$ and those from $y$. Pairs within the first block contribute the quadratic bit of $x$, and pairs within the second block contribute that of $y$. Every coordinate in the first block precedes every coordinate in the second, so the cross terms sum to $\sum_i\sum_j x_i y_j=(\sum_i x_i)(\sum_j y_j)$.

**Key facts.** `FABL.completeQuadraticBit_eq_full_sum`.
