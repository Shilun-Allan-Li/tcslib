<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.keepTrue_eq_nil_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Filtering True Bits

**Claim.** Removing all false entries from a finite Boolean list yields the empty list exactly when every entry of the original list is false.

**Proof.** Induct on the list. The empty list satisfies both conditions. For a head bit $b$ followed by a tail, if $b$ is false, filtering the list is just filtering the tail, and the induction hypothesis gives the desired equivalence. If $b$ is true, filtering retains that true bit, so the result cannot be empty; likewise, it is false that every entry is false. Thus both sides fail in this case.
