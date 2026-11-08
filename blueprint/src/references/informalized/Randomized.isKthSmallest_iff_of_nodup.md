<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.isKthSmallest_iff_of_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of the Kth Smallest Value

**Claim.** For a list $l$ of distinct elements in a linearly ordered set, $y$ satisfies the defining rank conditions for being the $k$th smallest value exactly when $y$ occurs in $l$ and exactly $k$ entries of $l$ are at most $y$.

**Proof.** For every list and value $y$, the number of entries at most $y$ is the number strictly below $y$ plus the number equal to $y$ (`Randomized.countP_le_eq_countP_lt_add_count`). Since $l$ has no repetitions and $y$ occurs in it, the equality count is one. Thus the number at most $y$ is one more than the number strictly below it. The defining rank inequalities, together with this identity, are equivalent to saying that the number at most $y$ is exactly $k$, in both directions.

**Key facts.** `Randomized.countP_le_eq_countP_lt_add_count`.
