<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.parityTuple_sum_le_matchingLabeling_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity and Matching Sum Comparison

**Claim.** For every $n,k,q$ and every real-valued function on the $n$-dimensional sign cube, the sum of parity-tuple Fourier weights is at most $(k!)^{-q}$ times the sum of matching-labeling Fourier weights.

**Proof.** Let $m=(k!)^q$, the number of ways to order the $k$ vertices in each of the $q$ parts; the reordering count is $k!^q$ (`FABL.card_parityTupleReordering`). For each parity tuple, pair it with one of these $m$ reorderings and use the parity-tuple-to-matching lift. This lift is injective (`FABL.parityTupleMatchingLift_injective`), so its outputs are distinct matching labelings, and each output has exactly the Fourier weight of its original tuple (`FABL.parityTupleMatchingLift_weight`). The general injective-lift averaging inequality says that when target weights are nonnegative, the sum of source weights is at most $1/m$ times the sum of all target weights (`FABL.sum_le_inv_mul_sum_of_injective_lifts`). The target weights here are products of absolute values, hence nonnegative. Applying that inequality gives the claimed factor $1/(k!)^q=(k!)^{-q}$.

**Key facts.** `FABL.card_parityTupleReordering`, `FABL.parityTupleMatchingLift_injective`, `FABL.parityTupleMatchingLift_weight`, `FABL.sum_le_inv_mul_sum_of_injective_lifts`.
