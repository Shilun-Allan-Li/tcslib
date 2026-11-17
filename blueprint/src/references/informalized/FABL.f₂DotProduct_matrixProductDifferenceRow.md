<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.f₂DotProduct_matrixProductDifferenceRow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing with a Matrix Difference Row

**Claim.** The dot product of row i of C′−AB with x equals the i-th coordinate of (C′−AB)x.

**Proof.** Both sides are the same finite sum: the i-th coordinate of a matrix-vector product is the sum over j of the matrix entry in row i and column j multiplied by xⱼ. For the matrix C′−AB, this is exactly the dot product of its i-th row with x.
