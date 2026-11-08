<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.sum_longPath_inversePathSize_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Sizes of Long Paths

**Claim.** For a finite list of paths, the sum of $2^{-length(p)}$ over paths longer than $k$ is at most the list length times $2^{-k}$.

**Proof.** Bound each list entry’s contribution separately. If a path has length greater than $k$, its inverse size is at most $2^{-k}$, since inverse path size decreases as the path length increases (`FABL.F₂DecisionTree.inversePathSize_le_inverseTwoPow`). If its length is not greater than $k$, its contribution is zero, also at most $2^{-k}$. Thus every weight in the list is bounded by $2^{-k}$. The sum of weights each bounded by $B$ is at most the list length times $B$ (`FABL.F₂DecisionTree.sum_map_le_length_mul`), proving the result.

**Key facts.** `FABL.F₂DecisionTree.inversePathSize_le_inverseTwoPow`, `FABL.F₂DecisionTree.sum_map_le_length_mul`.
