<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.FinOracleTM.exists_plain_simulation_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Plain simulation with a monotone bound

**Claim.** A finite oracle machine whose oracle language is decided within a nondecreasing bound can be simulated by a finite ordinary Turing machine with at least one additional work tape, with the stated time bound for every halting run from the specified tape contents.

**Proof.** Start with the general simulation theorem (\texttt{Turing.FinOracleTM.exists_plain_simulation}). It provides $P$ and $a$, preserves the output, and bounds the simulation time by a quadratic overhead plus a sum of the costs of the queries actually made. For each time $r<t$, if the oracle machine is in its query state, the blank query tape initially and its head position at the origin imply that the query written by time $r$ has length at most $r$ (\texttt{Turing.OracleTM.queryString_runFrom_length_le_of_blank}). Since $r<t$ and $\tau$ is nondecreasing, the cost $\tau(|v_r|)$ is at most $\tau(t)$. When the machine is not querying, the summand is zero, so every summand is bounded by $\tau(t)$. There are $t$ indices in the sum, hence the sum of query costs is at most $t\tau(t)$. Substituting this into the simulation bound gives $a(t+1)^2+a t\tau(t)$. This is at most $a(t+1)^2+a(t+1)\tau(t)$, which factors as $a(t+1)(t+1+\tau(t))$. The same witnesses for the simulated run therefore satisfy the sharper claimed bound.

**Key facts.** `Turing.FinOracleTM.exists_plain_simulation`, `Turing.OracleTM.queryString_runFrom_length_le_of_blank`.
