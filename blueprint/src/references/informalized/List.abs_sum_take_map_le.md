<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.abs_sum_take_map_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound for a truncated mapped sum

**Claim.** If every value $f(x)$ on a finite list has absolute value at most $B$, then the absolute value of the sum of the first $k$ mapped values is at most the list length times $B$.

**Proof.** The absolute value of the sum of the first $k$ mapped values is at most the sum of their absolute values, by the prefix triangle inequality (List.abs_sum_take_le_sum_abs). Each mapped absolute value is at most $B$ by hypothesis. The sum of these nonnegative values is therefore at most the number of mapped entries times $B$; there are at most as many such entries as the original list has entries. This yields the stated bound.

**Key facts.** `List.abs_sum_take_le_sum_abs`.
