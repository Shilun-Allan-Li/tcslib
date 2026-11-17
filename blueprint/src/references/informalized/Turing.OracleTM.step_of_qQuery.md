<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleCall.lean :: Turing.OracleTM.step_of_qQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query-state transition

**Claim.** When a configuration is in the query state, one step leaves every component except its state unchanged, setting the state according to whether its query string belongs to the oracle language.

**Proof.** Unfold the definition of the step. The hypothesis that the configuration state is the query state selects the oracle-query branch, which replaces only the state with the positive-answer state when the query string belongs to the oracle and the negative-answer state otherwise. The remaining configuration fields are preserved by the record update.
