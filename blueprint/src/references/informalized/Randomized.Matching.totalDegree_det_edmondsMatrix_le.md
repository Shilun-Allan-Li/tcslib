<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.totalDegree_det_edmondsMatrix_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Bound for the Edmonds Determinant

**Claim.** The total degree of the determinant of the Edmonds matrix specified by $A$ is at most $n$.

**Proof.** Expand the determinant as a sum over permutations: each summand is a signed coefficient times the product of the entries selected by one permutation ( `det_edmondsMatrix_eq_sum`). The total degree of a finite sum is bounded by the largest total degree among its summands, and the degree of a product is bounded by the sum of the degrees of its factors. The signed coefficient is constant, so it contributes degree zero. Each selected matrix entry is either a variable, of degree one, or zero, whose total degree is zero. Thus for every permutation the sum of the degrees of its $n$ factors is at most $n$. Taking the finite sum over permutations preserves this upper bound, proving the result.

**Key facts.** `Randomized.Matching.det_edmondsMatrix_eq_sum`.
