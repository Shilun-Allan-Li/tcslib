<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_workTapes_invariant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Locality of Initialized Runs

**Claim.** For every time $t$, every work-tape head in the run from the initial configuration is at distance at most $t$ from the origin, and every cell whose distance from the origin is at least $t$ is blank.

**Proof.** Apply the run-radius bound (`Turing.OracleTM.runFrom_radius`) to each tape, taking the initial radius to be $0$. The initial configuration has every head at position $0$ and every tape cell blank, so the lemma gives head distance at most $0+t=t$ and blankness outside that radius. Rewriting the radius inequality gives exactly the two asserted bounds.

**Key facts.** `Turing.OracleTM.runFrom_radius`.
