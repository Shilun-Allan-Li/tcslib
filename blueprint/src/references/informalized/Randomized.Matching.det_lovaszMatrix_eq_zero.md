<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.det_lovaszMatrix_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lovász determinant vanishing

**Claim.** For a Boolean matrix whose associated bipartite graph has no perfect matching, the determinant of the matrix of chosen edge weights, with zero entries off the edges, is zero.

**Proof.** Evaluate the polynomial determinant of the Edmonds matrix by substituting each variable $X_{i,j}$ with its prescribed weight $a_{i,j}$. Evaluation commutes with taking determinants, so this gives the determinant of the weighted matrix (eval_det_edmondsMatrix). Since there is no perfect matching, the polynomial determinant is zero by det_edmondsMatrix_eq_zero. Evaluation sends zero to zero, and therefore the weighted determinant is zero as well.

**Key facts.** `Randomized.Matching.eval_det_edmondsMatrix`, `Randomized.Matching.det_edmondsMatrix_eq_zero`.
