<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.cntLt_succ_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count After Adding an Index

**Claim.** The count of indices below $j+1$ where $kf(i)<t$ is the count below $j$, plus one if $kf(j)<t$ and zero otherwise.

**Proof.** Counting a predicate over an initial segment of length $j+1$ consists of counting it on the first $j$ indices and then checking the new index $j$. The general successor formula for counts (`Nat.count_succ`) gives precisely the stated increment.
