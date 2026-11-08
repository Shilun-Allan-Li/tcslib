<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleHost_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Host Simulation Step

**Claim.** Under the stated bounds on the query tape and the assumed behavior of the query machine, the host machine reaches a stable encoding of the oracle machine’s one-step successor within the claimed time bound, preserving a suitable side tag.

**Proof.** Split according to whether $c$ is in the query state. If it is, apply the query-case simulation result ( `Turing.oracleHost_query`): it supplies a host run reaching the correctly encoded oracle successor, together with its time bound in terms of the query length, the distance to the origin, and the service time $t$. The hypothesis on the service machine provides such a positive $t$ and guarantees that the exit state has not occurred earlier. Since the query has length at most $r$, its service cost is bounded by the claimed expression; the remaining terms are absorbed by the larger coefficient $2a+13$ using the assumed distance and length bounds.

If $c$ is not in the query state, the query state has not been visited at time $0$. Apply the off-query simulation result (`Turing.oracleHost_offQuery`) for one step. It matches the host run with the oracle machine’s one-step run and supplies a side tag satisfying the required sign condition. The bound follows because $1\le (2a+13)(r+1)$, and the query-service term vanishes in this case.

**Key facts.** `Turing.oracleHost_query`, `Turing.oracleHost_offQuery`.
