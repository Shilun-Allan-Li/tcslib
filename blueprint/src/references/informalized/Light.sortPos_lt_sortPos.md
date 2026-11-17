<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.sortPos_lt_sortPos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct sorting positions are ordered

**Claim.** If $i<N$ and either $k(i)<k(j)$ or $k(i)=k(j)$ with $i<j$, then the position of $i$ is strictly less than the position of $j$.

**Proof.** There are two cases. If $k(i)<k(j)$, the position of $i$ is less than the count of values below $k(i)+1$ (`sortPos_lt_cntLt_succ`). Since $k(i)+1\le k(j)$, monotonicity of the count in its value threshold bounds that count by the number of values below $k(j)$ (`cntLt_mono_left`). The latter count is part of the position of $j$, so it is at most that position. If instead the values are equal and $i<j$, the counts of values below their common value agree. The number of earlier indices with that value before $i$ is strictly less than the corresponding number before $j$, by the equal-value count bound (`cntEq_lt_of_lt`). Adding the common count of smaller values gives the required strict inequality.

**Key facts.** `Light.sortPos_lt_cntLt_succ`, `Light.cntLt_mono_left`, `Light.cntEq_lt_of_lt`.
