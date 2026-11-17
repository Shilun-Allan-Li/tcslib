<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.cntLt_zero_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count Below Zero

**Claim.** No index $i<j$ satisfies $kf(i)<0$, so the count below zero is zero.

**Proof.** Natural numbers are never less than zero. Hence the predicate being counted is false at every index, and counting it over any initial segment gives zero.
