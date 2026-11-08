<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.countP_getElem_lt_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Larger Entries in a Sorted List

**Claim.** In a nondecreasing list $s$, for an index $j<|s|$, the number of entries strictly greater than $s_j$ is at most $|s|-1-j$.

**Proof.** Split the list after its first $j+1$ entries. None of those entries is greater than $s_j$: each earlier entry is at most $s_j$ by the nondecreasing order, and the entry at index $j$ equals itself. Hence all entries greater than $s_j$ lie in the remaining suffix. Their number is no larger than the length of that suffix, which is $|s|-(j+1)=|s|-1-j$.
