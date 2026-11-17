<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.det_edmondsMatrix_ne_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Determinant detects perfect matchings

**Claim.** The determinant of the polynomial matrix is nonzero exactly when the associated bipartite graph has a perfect matching.

**Proof.** For the forward direction, suppose the determinant is nonzero. If there were no perfect matching, the vanishing theorem (det_edmondsMatrix_eq_zero) would force the determinant to be zero, a contradiction. Conversely, suppose there is a perfect matching. By the characterization of perfect matchings by permutations (hasPerfectMatching_iff_exists_perm), choose a permutation $\tau$ whose selected entries are all true. The coefficient of the monomial associated with $\tau$ in the determinant is its sign, viewed in $R$ (coeff_det_edmondsMatrix). If the determinant were zero, this coefficient would be zero. But a permutation sign is a unit, hence is either $1$ or $-1$, and each remains nonzero in a nontrivial ring. This contradiction proves that the determinant is nonzero.

**Key facts.** `Randomized.Matching.det_edmondsMatrix_eq_zero`, `Randomized.Matching.hasPerfectMatching_iff_exists_perm`, `Randomized.Matching.coeff_det_edmondsMatrix`.
