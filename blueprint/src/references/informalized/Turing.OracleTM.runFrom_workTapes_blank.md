<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_workTapes_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Cells Beyond Elapsed Time

**Claim.** After $t$ steps from the initial configuration, every cell at integer position $z$ with $t\le |z|$ is blank on every work tape.

**Proof.** The run's work-tape invariant states that at every time $t$, every tape cell at distance at least $t$ from the origin is blank (`Turing.OracleTM.runFrom_workTapes_invariant`). Apply its blankness component to the given tape index and position $z$, using the assumed inequality $t\le |z|$.

**Key facts.** `Turing.OracleTM.runFrom_workTapes_invariant`.
