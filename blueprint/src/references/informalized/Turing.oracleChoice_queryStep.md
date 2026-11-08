<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleChoice_queryStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-step query-state simulation

**Claim.** Starting in the query state with the added tape scanning $b$, two steps of the constructed machine produce the lift of the original nondeterministic step using choice bit $b$, with the added tape head advanced to $p+1$.

**Proof.** Express the two-step run as one step after the first step (`OracleTM.runFrom_succ_eq_step'`). Since the starting state is the query state, that first step changes the state to the positive-answer or negative-answer state according to whether the query string belongs to $O$ (`OracleTM.step_of_qQuery`). Inserting the added choice tape has not changed the query string (`oracleChoiceCfg_query`), so this answer is the same one determined by the original configuration. The next step is an auxiliary-state pause: its state component records the query answer, and its head movement advances the added tape one cell. The underlying nondeterministic transition is identified with the corresponding fixed-choice deterministic transition (`OracleNDTM.stepWith_eq_fixChoice_step`); when the query answer is positive, use auxiliary state $0$, and when it is negative, use auxiliary state $1$. The pause-step calculation (`oracleChoice_pause`) then yields precisely the lift of that fixed-choice step, with head position $p+1$.

**Key facts.** `Turing.OracleTM.runFrom_succ_eq_step'`, `Turing.OracleTM.step_of_qQuery`, `Turing.oracleChoiceCfg_query`, `Turing.OracleNDTM.stepWith_eq_fixChoice_step`, `Turing.oracleChoice_pause`.
