<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.abs_sum_map_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on an integer sum

**Claim.** If every value $f(x)$ on a finite list has absolute value at most $B$, then the absolute value of the sum of those values is at most the list length times $B$.

**Proof.** Apply the bound for a truncated mapped sum with truncation length equal to the length of the original list. Taking that many entries from the mapped list leaves the whole mapped list, since mapping preserves length. The resulting inequality is exactly the desired bound.

**Key facts.** `List.abs_sum_take_map_le`.
