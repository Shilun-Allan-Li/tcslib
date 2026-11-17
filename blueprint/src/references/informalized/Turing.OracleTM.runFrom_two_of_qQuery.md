<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleCall.lean :: Turing.OracleTM.runFrom_two_of_qQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two Steps after an Oracle Query

**Claim.** When the machine is in its query state, two steps halt and append the symbol prescribed by whether the query string belongs to the oracle, leaving all other configuration data unchanged.

**Proof.** Rewrite two steps as two successive one-step transitions using the run successor equation (`Turing.OracleTM.runFrom_succ_eq_step'`). Since the starting state is the query state, the query-step theorem (`Turing.OracleTM.step_of_qQuery`) says the first step changes only the state, choosing the positive-answer state when the query belongs to $O$ and the negative-answer state otherwise. Split into these two membership cases. In the positive case, the query state differs from the positive-answer state by well-formedness, and its transition is the specified answer action; the answer-action theorem (`Turing.OracleTM.step_of_answerAction`) therefore halts and appends $y$. In the negative case, the query state differs from the negative-answer state, and the same theorem applied to the specified negative transition halts and appends $z$. In both cases the resulting configuration has the asserted state and output, with the other components unchanged.

**Key facts.** `Turing.OracleTM.runFrom_succ_eq_step'`, `Turing.OracleTM.step_of_qQuery`, `Turing.OracleTM.step_of_answerAction`.
