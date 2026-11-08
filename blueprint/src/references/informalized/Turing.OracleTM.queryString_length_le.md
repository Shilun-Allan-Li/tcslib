<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.queryString_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Length Bounded by Running Time

**Claim.** The query string in the configuration reached after $t$ steps from the initial configuration has length at most $t$.

**Proof.** Apply the blank-cell query-length bound (`Turing.OracleTM.queryString_length_le_of_blank`) with $n=t$. It remains to establish that the query tape is blank at position $t$. The run invariant (`Turing.OracleTM.runFrom_workTapes_invariant`) says that every cell whose absolute position is at least $t$ is blank in the configuration reached after $t$ steps. At position $t$, the absolute value is $t$, so this cell is blank. The blank-cell bound now gives that the query string has length at most $t$.

**Key facts.** `Turing.OracleTM.runFrom_workTapes_invariant`, `Turing.OracleTM.queryString_length_le_of_blank`.
