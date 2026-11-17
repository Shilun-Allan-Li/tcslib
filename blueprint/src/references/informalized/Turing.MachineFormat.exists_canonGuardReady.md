<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonGuardReady -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guard Check from Ready Tapes

**Claim.** Given a machine format $F$ and $k\ge4$, a finite-state machine with $k$ work tapes checks the canonical guard condition from the prescribed ready words in linear time, reaches the corresponding exit state, and preserves the specified tapes and first-exit property.

**Proof.** Reserve tape 1 for the binary counter and tapes 2 and 3 for the offset and scratch bank. The seeker supplied for this two-tape bank moves the input head to the offset specified by the canonical offset word, while leaving the other tapes fixed. Its running-time bound is linear in the input length because the offset word has length at most $|bits|+2$ and its encoded position is at most $|x|+1$. At the seeker's exit, the canonical guard-on-bank result runs the binary guard checker using tape 1. If the guard condition fails, the checker exits at the right end. If it succeeds, its input head has passed the target; run the seeker again to return to the target position. Embedding the counter machine on tape 1 preserves all tapes other than that tape. In each branch the resulting configuration has the stated exit, empty output, head position, and unchanged ready contents off tape 1. The cut properties of the guard and seeker, together with seam composition and its first-return avoidance property, ensure no indexed exit is reached earlier. Adding the seek, guard, and possible return costs gives a bound by a constant times $|x|+1$.

**Key facts.** `Turing.MachineFormat.exists_canonSeekOnBank`, `Turing.MachineFormat.canonOffset_spec`, `Turing.MachineFormat.canonGuard_onBank`, `Turing.MachineFormat.canonSeam_avoids`, `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_runFrom_left`.
