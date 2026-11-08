<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.eval_det_edmondsMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Edmonds determinant

**Claim.** Evaluating the determinant of the polynomial matrix at the specified weights gives the determinant of the matrix whose entries are those weights on true positions and zero elsewhere.

**Proof.** Evaluation is a ring homomorphism, so it commutes with the determinant. It remains to compare the evaluated polynomial matrix entry by entry with the weighted matrix. At a position where the Boolean entry is true, evaluation sends the variable $X_{i,j}$ to $a_{i,j}$; where it is false, evaluation sends zero to zero. Thus the matrices agree, and so do their determinants.
