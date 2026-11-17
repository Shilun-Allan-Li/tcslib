<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.det_edmondsMatrix_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing without a perfect matching

**Claim.** If the bipartite graph associated with the Boolean matrix has no perfect matching, then the determinant of its polynomial matrix is zero.

**Proof.** The characterization of perfect matchings by permutations (hasPerfectMatching_iff_exists_perm) says that the absence of a perfect matching means every permutation has some index $i$ for which $A_{i,\sigma(i)}$ is false. Expand the determinant as a sum over permutations, using the permutation expansion of the determinant (det_edmondsMatrix_eq_sum). For each permutation, the factor at that index in the product of matrix entries is zero, since the corresponding matrix entry is zero when the Boolean entry is false. Thus every summand vanishes, so the determinant is zero.

**Key facts.** `Randomized.Matching.hasPerfectMatching_iff_exists_perm`, `Randomized.Matching.det_edmondsMatrix_eq_sum`.
