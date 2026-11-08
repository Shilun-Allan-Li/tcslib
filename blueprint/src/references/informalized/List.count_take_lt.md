<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.count_take_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A prefix count is smaller

**Claim.** If position $i$ is within a finite list and its entry is $x$, then the count of $x$ among the first $i$ entries is strictly less than its count in the whole list.

**Proof.** The list of the first $i+1$ entries is a sublist of the whole list, so its count of $x$ is at most the count in the whole list. The count formula for adjoining the entry at position $i$ (List.count_take_succ_getD) says that the $(i+1)$-prefix count is the $i$-prefix count plus one when that entry is $x$. By hypothesis it is $x$, so the whole-list count is at least the prefix count plus one. Hence the prefix count is strictly smaller.

**Key facts.** `List.count_take_succ_getD`.
