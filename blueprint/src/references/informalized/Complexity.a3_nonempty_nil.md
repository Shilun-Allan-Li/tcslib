<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_nonempty_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-Input Rejection by the Guard

**Claim.** On empty input, the nonempty-input guard halts after one step and outputs exactly $[\mathrm{false}]$, with some amount of work-tape space.

**Proof.** The initial configuration is in the guard state, with empty input, blank work tapes, and empty output. Since the input head sees no symbol, the guard’s transition enters the halting state and appends the single symbol false to the output. Thus after one step the run is halted with output $[\mathrm{false}]$. The characterization of computation by the halted state and output gives a witness for the required space value (`computesInTime_iff`).

**Key facts.** `Turing.FinTM.computesInTime_iff`.
