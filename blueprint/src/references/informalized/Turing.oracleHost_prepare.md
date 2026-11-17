<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleHost_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparing the oracle service phase

**Claim.** When the oracle machine is in its query state and the query-head position has the specified side, the host reaches the service sweep configuration within the stated bound.

**Proof.** Write $f$ for the query-tape contents and $p$ for its head position. The dispatch preparation lemma (`Turing.oraclePrepare`) gives a local dispatch run from the bookmark state to the ready configuration, of length at most $|p|+3$, and ensures that every earlier state is one of bookmark, origin, or save. The source phase first redirects the query-state configuration to the dispatch bookmark state. The source-to-dispatch local-view identity (`Turing.oracleSource_localView`) identifies the resulting host tapes with the embedding of the local bookmark configuration. Apply the host dispatch simulation theorem (`Turing.oracleHost_dispatch`) to the preparation run: its guard holds because bookmark, origin, and save are internal. Its endpoint is the copy state, which redirects to the service sweep state. Concatenate the initial redirect step with this simulated dispatch run and its redirect step, using run composition (`Turing.MultiTapeTM.runFrom_add`). The total is $1+(t+1)$, which is at most $|p|+5$ from the preparation bound.

**Key facts.** `Turing.oraclePrepare`, `Turing.oracleSource_localView`, `Turing.oracleHost_dispatch`, `Turing.MultiTapeTM.runFrom_add`.
