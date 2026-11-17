<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.four_mul_sum_max_countP_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A bound on list order counts

**Claim.** For a finite list $l$ in a linearly ordered type, the sum over its entries of the larger of the counts strictly below and strictly above each entry, multiplied by $4$, is at most $3|l|^2$.

**Proof.** Sort $l$ into a nondecreasing list $s$. Sorting preserves the entries with their multiplicities and preserves length. Thus the sum of the original order-count expression can be computed over the entries $s_j$ of the sorted list, using the counts in $s$. For each position $j$, at most $j$ entries of $s$ are strictly below $s_j$, and at most $|s|-1-j$ are strictly above it (`countP_lt_getElem_le`, `countP_getElem_lt_le`). Therefore the larger count at that position is at most $\max(j,|s|-1-j)$. Summing these bounds over all positions reduces the claim to $4\sum_{j<|s|}\max(j,|s|-1-j)\le3|s|^2$ (`four_mul_sum_max_le`). Since sorting does not change length, this is the desired bound for $l$.

**Key facts.** `Randomized.countP_lt_getElem_le`, `Randomized.countP_getElem_lt_le`, `Randomized.four_mul_sum_max_le`.
