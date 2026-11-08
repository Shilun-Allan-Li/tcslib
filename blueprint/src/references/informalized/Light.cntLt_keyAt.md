<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/StablePass.lean :: Light.cntLt_keyAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Count for List Keys

**Claim.** For a finite list, the number of positions whose key under $kd$ is less than $s$ equals the number of list entries $i$ with $kd(i)<s$.

**Proof.** Proceed by induction on the list, using the reverse-list recursion that appends one final element. The empty list has both counts zero. For a list of the form $l$ followed by $x$, first observe that at every position below the length of $l$, the default-indexed lookup in the extended list agrees with the lookup in $l$. The prefix-agreement result (`Light.cntLt_congr`) therefore identifies the count on that prefix with the count for $l$. The count-successor formula (`Light.cntLt_succ_right`) then says that extending the prefix adds one precisely when the key at the new last position is below $s$; that key is $kd(x)$. By the induction hypothesis, the prefix count is the number of entries of $l$ whose keys are below $s$. Appending $x$ adds exactly one to the list count if $kd(x)<s$, and zero otherwise, so the two sides agree.

**Key facts.** `Light.cntLt_congr`, `Light.cntLt_succ_right`.
