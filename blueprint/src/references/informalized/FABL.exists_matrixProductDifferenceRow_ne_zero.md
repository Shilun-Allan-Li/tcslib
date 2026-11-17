<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.exists_matrixProductDifferenceRow_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Nonzero Difference Row

**Claim.** If $C'\ne AB$, then at least one row of $C'-AB$ is nonzero.

**Proof.** The matrix difference $C'-AB$ is nonzero, since a zero difference would give $C'=AB$. Suppose every row of this difference were zero. Then for every row index $i$ and column index $j$, its $(i,j)$ entry would be zero. Matrices are equal when all their entries agree, so the difference would be the zero matrix, a contradiction. Thus some row is nonzero.
