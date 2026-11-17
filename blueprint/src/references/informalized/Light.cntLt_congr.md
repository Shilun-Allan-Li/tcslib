<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.cntLt_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Count Agreement

**Claim.** If two functions agree at every index below $m$, then their counts of indices below $m$ where the function value is less than $s$ are equal.

**Proof.** Each index below $m$ satisfies $kf(i)<s$ exactly when it satisfies $kf'(i)<s$, because the function values agree there. Thus the first predicate implies the second, giving one inequality between the counts by monotonicity of counting predicates; reversing the roles gives the opposite inequality. The counts are therefore equal.
