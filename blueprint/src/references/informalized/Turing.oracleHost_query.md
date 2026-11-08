<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleHost_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Query Simulation

**Claim.** The host simulates one oracle query step: from a stable encoding of a query configuration, it reaches a stable encoding of the oracle-step successor within the stated time bound, with a side tag consistent with the successor query-head position.

**Proof.** First, the host’s preparation procedure moves from the stable source encoding into the service phase, positioning the query data for the call; it takes at most $|p|+5$ steps (`Turing.oracleHost_prepare`). The service phase then copies the query word, runs the answer machine, and returns the verdict in the dispatch encoding after exactly $2|z|+4+t$ steps (`Turing.oracleHost_service`). Finally, the restoration procedure returns the host to a stable source encoding of the answer-updated configuration, preserving the query-head side condition (`Turing.oracleHost_restore`). Concatenating these runs is justified by the fact that a run of length $a+b$ is the run of length $a$ followed by one of length $b$ (`Turing.MultiTapeTM.runFrom_add`). The query-state rule for the oracle machine identifies the target configuration as precisely the one with state set according to whether $z\in O$ (`Turing.OracleTM.step_of_qQuery`). The three time contributions are bounded by $2|p|+2|z|+t+13$ using the preparation and restoration bounds and elementary arithmetic; the returned tag and configuration are those supplied by restoration.

**Key facts.** `Turing.oracleHost_prepare`, `Turing.oracleHost_service`, `Turing.oracleHost_restore`, `Turing.MultiTapeTM.runFrom_add`, `Turing.OracleTM.step_of_qQuery`.
