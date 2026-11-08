<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.sortPos_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sorting positions stay in range

**Claim.** For $j<N$, the position assigned to $j$ by sorting the first $N$ indices by value, with ties broken by index, is less than $N$.

**Proof.** The position of $j$ is strictly less than the number of indices among the first $N$ whose value is at most $k(j)$, expressed as the count of values less than $k(j)+1$ (`sortPos_lt_cntLt_succ`). That count is at most $N$, since it counts a subset of the first $N$ indices (`cntLt_le`). Therefore the position is strictly less than $N$.

**Key facts.** `Light.sortPos_lt_cntLt_succ`, `Light.cntLt_le`.
