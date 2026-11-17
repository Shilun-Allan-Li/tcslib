<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.spaceUsedByTape_le_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Per-Tape Space Bound

**Claim.** For any work tape, the number of distinct cells it visits through step $t$ is at most the total space used through that step.

**Proof.** Total space is the sum, over all work tapes, of the number of distinct cells visited on each tape. Each summand is a natural number and hence nonnegative, so any one summand is at most the whole sum.
