<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleNDTM.queryString_runWith_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Length Bound

**Claim.** The query word on the final query tape after running on $w$ from the initial configuration has length at most $|w|$.

**Proof.** Apply the work-tape invariant to the query tape, taking the nonnegative position $|w|$. The invariant says that every tape cell at a position whose absolute value is at least $|w|$ is blank. In particular, the cell at position $|w|$ is blank. The query-string length bound for a tape blank at position $n$ then gives query length at most $n$; set $n=|w|$.

**Key facts.** `Turing.OracleNDTM.runWith_workTapes_invariant`, `Turing.OracleTM.queryString_length_le_of_blank`.
