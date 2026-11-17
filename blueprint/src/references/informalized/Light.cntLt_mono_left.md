<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.cntLt_mono_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Count Monotonicity

**Claim.** If $s\le t$, then the number of indices below $j$ where $kf$ is less than $s$ is at most the number where it is less than $t$.

**Proof.** Whenever $kf(i)<s$ and $s\le t$, transitivity gives $kf(i)<t$. Thus the indices counted at threshold $s$ are included among those counted at threshold $t$. Monotonicity of counting under predicate implication (`Nat.count_mono_left`) gives the claimed inequality.
