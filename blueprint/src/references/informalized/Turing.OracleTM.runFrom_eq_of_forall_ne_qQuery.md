<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_eq_of_forall_ne_qQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Before a Query

**Claim.** If the run using $O$ is never in the query state at any time before $t$, then the two runs from the same configuration agree after $t$ steps.

**Proof.** Proceed by induction on $t$. At time zero both runs are at the given configuration. For the successor case, the induction hypothesis gives equality of the configurations reached at time $t$ under the two oracles, because the assumed non-query condition also holds at every earlier time. At time $t$ itself the run using $O$ is not in the query state. The one-step updates from this common configuration therefore agree for the two oracles, by the fact that a non-query step is independent of the oracle (Turing.OracleTM.step_eq_of_ne_qQuery). The successor-step description of a run (Turing.OracleTM.runFrom_succ_eq_step') now gives equality at time $t+1$.

**Key facts.** `Turing.OracleTM.runFrom_succ_eq_step'`, `Turing.OracleTM.step_eq_of_ne_qQuery`.
