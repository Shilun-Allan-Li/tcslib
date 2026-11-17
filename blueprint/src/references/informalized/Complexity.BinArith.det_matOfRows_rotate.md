<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetModMath.lean :: Complexity.BinArith.det_matOfRows_rotate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Determinant under cyclic row rotation

**Claim.** Appending $r_0$ after the rows of $R$ changes the determinant by the factor $(-1)^{|R|}$ compared with placing $r_0$ first.

**Proof.** The rows of the matrix formed from $R$ followed by $r_0$ are the rows of the matrix formed from $r_0$ followed by $R$, reordered by the cyclic permutation that moves the first row to the last position. The proof first verifies this row correspondence, including the final row, directly from list indexing. Permuting rows multiplies the determinant by the sign of the permutation, and this cyclic permutation has sign $(-1)^{|R|}$.
