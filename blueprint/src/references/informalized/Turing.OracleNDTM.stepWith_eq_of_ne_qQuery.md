<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleNDTM.stepWith_eq_of_ne_qQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Independence Away From Query States

**Claim.** If a configuration is not in the query state, then its step using choice $b$ is the same for either oracle language $O_1$ or $O_2$.

**Proof.** Translate each nondeterministic step using choice $b$ into a step of the deterministic machine obtained by fixing that choice. The configuration's state differs from the machine's query state, so the deterministic machine's step is independent of the oracle language. Thus its steps relative to $O_1$ and $O_2$ agree; translating back gives the desired equality.

**Key facts.** `Turing.OracleNDTM.stepWith_eq_fixChoice_step`, `Turing.OracleTM.step_eq_of_ne_qQuery`.
