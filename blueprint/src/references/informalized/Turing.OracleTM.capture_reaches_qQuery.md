<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleCall.lean :: Turing.OracleTM.capture_reaches_qQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Computation Reaches the Query State

**Claim.** Under the stated transition-agreement and state-avoidance hypotheses, if the original machine is halted after $T$ steps, then the oracle machine reaches the capture of that final configuration at some time $u\le T$.

**Proof.** Choose the first halting time $u$ of the original computation. It is at most $T$, the computation is still live at every earlier time, and its configuration at time $u$ equals its configuration at time $T$ (`Turing.MultiTapeTM.exists_first_halt`). The transition-agreement hypothesis also holds for the oracle machine with the empty oracle: away from its query state its transition is the specified capture transition, and the embedded states avoid the query state. The capture-run theorem therefore shows, for every time up to $u$, that this empty-oracle machine's configuration is the capture of the original machine's configuration at that time (`Turing.capture_run`). In particular this holds at $u`. At every time strictly before $u$, the original computation is live, so its captured state is an embedded state and hence is not the oracle machine's query state. The oracle-run comparison theorem then identifies the run with oracle $O$ through time $u$ with the empty-oracle run (`Turing.OracleTM.runFrom_eq_plainEmptyOracle`). Combining these equalities, the oracle run at time $u$ is the capture of the original configuration at $u$, which is also the capture of its configuration at $T$.

**Key facts.** `Turing.MultiTapeTM.exists_first_halt`, `Turing.capture_run`, `Turing.OracleTM.runFrom_eq_plainEmptyOracle`.
