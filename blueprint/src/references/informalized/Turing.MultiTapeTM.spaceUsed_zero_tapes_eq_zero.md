<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Space with No Work Tapes

**Claim.** If the machine has no work tapes, then its total space use through any step $t$ is zero.

**Proof.** Total space is the sum over work-tape indices of the number of distinct cells visited on each tape. When $k=0$, there are no such indices, so this is an empty sum, which equals zero.
