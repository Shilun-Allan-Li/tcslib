<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.cntLt_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Count Bound

**Claim.** The number of indices below $j$ where $kf$ is less than $t$ is at most $j$.

**Proof.** There are exactly $j$ indices below $j$, and the indices satisfying the additional condition $kf(i)<t$ form a subset of them. Hence their count is at most $j$, by the general bound that a count over an initial segment does not exceed its length (`Nat.count_le`).
