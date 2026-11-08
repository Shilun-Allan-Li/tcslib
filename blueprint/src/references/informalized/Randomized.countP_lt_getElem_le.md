<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.countP_lt_getElem_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rank Bound in a Sorted List

**Claim.** In a nondecreasing finite list $s$, for any valid index $j$, at most $j$ entries are strictly less than the entry at index $j$.

**Proof.** Split $s$ into the prefix of length $j$ and the suffix beginning at index $j$. Counts over a concatenation add. No entry in the suffix is strictly less than $s[j]$: its first entry is $s[j]$, and each later entry is at least $s[j]$ by the pairwise nondecreasing hypothesis. The count is therefore entirely in the prefix. The number of qualifying entries in that prefix is at most its length, which is $j$, proving the bound.
