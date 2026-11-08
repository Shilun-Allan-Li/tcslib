<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleHost_dispatch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle host dispatch simulation

**Claim.** A dispatch run of length $T$ that ends in a state redirected to phase state $q'$ is simulated by the host machine in $T+1$ steps, with the final state replaced by $q'$, provided every earlier dispatch state is internal.

**Proof.** First use the tape-embedding simulation theorem (`Turing.embedEmitTM_runFrom`): running the dispatch machine on its four selected host tapes agrees for $T$ steps with embedding its local run into the host tapes. The selected slots are distinct, as supplied by the injectivity fact (`Turing.oracleSlots_injective`), so this is a valid embedding. Now apply the phase-host run theorem (`Turing.phaseHostTM_run`) to the embedded run. Its hypothesis that no earlier state redirects follows from the guard: every state before time $T$ is internal, and the internal-state predicate excludes the ready, copy, and answer states, which are precisely the dispatch states that redirect. Thus the host follows the embedded dispatch run through time $T$, then performs one redirect step from the endpoint state $s'$ to $q'$.

**Key facts.** `Turing.embedEmitTM_runFrom`, `Turing.oracleSlots_injective`, `Turing.phaseHostTM_run`.
