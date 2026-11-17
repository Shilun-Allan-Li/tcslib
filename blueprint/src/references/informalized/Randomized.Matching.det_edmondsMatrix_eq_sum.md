<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.det_edmondsMatrix_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation expansion of the determinant

**Claim.** The determinant of the polynomial matrix is the sum over all permutations of their signs times the products of the corresponding entries.

**Proof.** Transpose the matrix and apply the determinant expansion indexed by permutations. The transpose identity identifies its determinant with the original determinant, while the permutation expansion for the transpose has factors from the original matrix in the order $M_{i,\sigma(i)}$. Unfolding the matrix entries makes the resulting expression exactly the stated sum.
