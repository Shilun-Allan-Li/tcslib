<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.FiniteDecisionTree.deterministicQueryProbability_permuteCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query probability under coordinate permutations

**Claim.** For every coordinate permutation and coordinate $i$, the probability that the permuted tree queries $i$ equals the probability that the original tree queries $σ^{-1}(i)$.

**Proof.** Unfold query probability as the product mean of the indicator that the coordinate occurs in the query trace. For each input, the permuted tree queries $i$ exactly when the original tree queries $σ^{-1}(i)$ on the reindexed input $x'(j)=x(σ(j))$; this is the coordinate-permutation correspondence for queries (FiniteDecisionTree.queries_permuteCoordinates_iff). Thus the first indicator is the second indicator composed with the input reindexing. Invariance of the product mean under that permutation gives the equality (productMean_comp_permuteInput).

**Key facts.** `FABL.FiniteDecisionTree.queries_permuteCoordinates_iff`, `FABL.productMean_comp_permuteInput`.
