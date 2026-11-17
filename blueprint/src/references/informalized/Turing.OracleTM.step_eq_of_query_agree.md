<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleTM.step_eq_of_query_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step Equality When Query Answers Agree

**Claim.** If the two oracle languages agree on the query string whenever the configuration is in the query state, then the resulting one-step configurations agree.

**Proof.** Separate the case that the configuration is in the query state from the case that it is not. In the query-state case, the assumed equivalence of membership answers makes the conditional successor state identical for both oracle languages, so the resulting configurations agree. Outside the query state, the step is oracle-independent by the step-independence result (`Turing.OracleTM.step_eq_of_ne_qQuery`).

**Key facts.** `Turing.OracleTM.step_eq_of_ne_qQuery`.
