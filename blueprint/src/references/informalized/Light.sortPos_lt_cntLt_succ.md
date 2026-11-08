<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.sortPos_lt_cntLt_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sorting position and value counts

**Claim.** For $j<N$, the position of $j$ is strictly less than the number of indices among the first $N$ whose value is less than $k(j)+1$.

**Proof.** The count of values less than $k(j)+1$ splits into the count of values less than $k(j)$ plus the count equal to $k(j)$ (`cntLt_succ_left`). The position of $j$ is the first of these counts plus the number of earlier indices, below $j$, whose value equals $k(j)$. Because $j<N$, that earlier-index count is strictly less than the count of indices below $N$ whose value equals $k(j)$ (`cntEq_lt_of_lt`). Adding the common count of smaller values preserves the strict inequality, proving the claim.

**Key facts.** `Light.cntLt_succ_left`, `Light.cntEq_lt_of_lt`.
