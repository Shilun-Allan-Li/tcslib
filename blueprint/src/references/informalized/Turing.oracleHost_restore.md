<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleHost_restore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoring the Oracle Configuration

**Claim.** Starting from the specified dispatch encoding of a ready configuration with verdict $v$, the host reaches, after $|p|+4$ steps, a stable encoding of the configuration with its state changed to the appropriate oracle-answer state, for a side tag consistent with the query-head position.

**Proof.** Write $p$ for the query-head position. The dispatch restoration routine moves the query and bookkeeping heads back to their required locations and produces an answer state tagged by some side $b'$; it takes $|p|+3$ steps, preserves the side condition, and its intermediate dispatch states remain within the internal dispatch phase (`Turing.oracleRestore`, `Turing.oracleRestore_cut`). The host’s dispatch-phase simulation theorem then carries this run into the full host machine. Since the run avoids leaving the internal dispatch phase before its endpoint, the host performs the dispatch transitions and redirects at that endpoint to the source phase with state equal to the positive-answer state when $v$ is true and the negative-answer state otherwise (`Turing.oracleHost_dispatch`). At this point the resulting source configuration agrees with the stable encoding of the answer-updated original configuration: the local-view identity identifies the dispatch encoding’s tapes and heads with the source encoding, and the nonhalting hypothesis ensures the source state is represented correctly (`Turing.oracleSource_localView`). The dispatch simulation contributes one additional transition, giving the stated total of $|p|+4$.

**Key facts.** `Turing.oracleRestore`, `Turing.oracleRestore_cut`, `Turing.oracleHost_dispatch`, `Turing.oracleSource_localView`.
