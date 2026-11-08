<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleOffQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation Away from Oracle Queries

**Claim.** If the empty-oracle computation avoids the query state at every time before $t$, then the host machine’s transitions agree with the oracle computation through time $t$, with a side tag maintaining the required sign condition.

**Proof.** First establish that every state encountered by the shadow simulation before time $t$ has an underlying machine state different from the query state. The shadow-run invariant (`Turing.oracleShadow_run`) relates each shadow configuration to the empty-oracle run and preserves the side condition; projecting its state to the underlying machine state, the hypothesis that the empty-oracle run avoids the query state gives this claim.

Now apply the run-transfer theorem for machines whose transitions agree on all states reached before the endpoint (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`). The assumed transition agreement applies at each such state, so the host run equals the embedded shadow run at time $t$. Finally, the shadow-run invariant supplies a side tag for the endpoint and identifies the shadow configuration there with the encoding of the empty-oracle configuration. Since the empty-oracle and oracle runs agree through time $t$ when no earlier query state was visited (`Turing.OracleTM.runFrom_eq_plainEmptyOracle`), this is the required encoding of the oracle run. The embedding-run identity (`Turing.embedEmitTM_runFrom`) converts the embedded machine run to the stated encoded configuration.

**Key facts.** `Turing.oracleShadow_run`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.OracleTM.runFrom_eq_plainEmptyOracle`, `Turing.embedEmitTM_runFrom`.
