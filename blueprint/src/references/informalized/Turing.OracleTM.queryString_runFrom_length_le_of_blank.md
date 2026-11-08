<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.OracleTM.queryString_runFrom_length_le_of_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Length During a Run

**Claim.** Starting with the query tape blank at every cell and its head at position $0$, after $s$ steps the query string has length at most $s$.

**Proof.** Apply the run-radius bound to the query tape with initial radius $0$. The head begins within that radius, and every cell at distance at least $0$ is blank by hypothesis. After $s$ steps, the bound says that every cell whose absolute position is at least $s$ is blank. In particular, the cell at position $s$ is blank. The query-length bound for a blank cell then gives query-string length at most $s$.

**Key facts.** `Turing.OracleTM.runFrom_radius`, `Turing.OracleTM.queryString_length_le_of_blank`.
