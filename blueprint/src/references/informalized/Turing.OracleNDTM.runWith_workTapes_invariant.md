<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleNDTM.runWith_workTapes_invariant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Bounds

**Claim.** After the computation driven by the choice sequence $w$, every work-tape head lies within distance $|w|$ of cell $0$, and every cell at distance at least $|w|$ from $0$ is blank.

**Proof.** Apply the head-and-blank invariant to the initial configuration with $n=0$. Initially every head is at $0$, and every cell is blank, so both hypotheses of the invariant hold. It follows that after the choices in $w$, every head has absolute position at most $0+|w|$, and every cell whose absolute position is at least $0+|w|$ is blank. Simplifying these bounds gives the claim.

**Key facts.** `Turing.runWith_headBlank`.
