<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.abs_sum_take_le_sum_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute sum of a prefix

**Claim.** The absolute value of the sum of the first $k$ entries of a finite list is at most the sum of the absolute values of all its entries.

**Proof.** First, the absolute value of the prefix sum is at most the sum of the absolute values within that prefix, by the triangle inequality for list sums (List.abs_sum_le_sum_abs). The prefix is a sublist of the original list. Summing a nonnegative function over a sublist gives at most its sum over the full list; here the function is absolute value, which is nonnegative. Combining these inequalities proves the claim.

**Key facts.** `List.abs_sum_le_sum_abs`.
