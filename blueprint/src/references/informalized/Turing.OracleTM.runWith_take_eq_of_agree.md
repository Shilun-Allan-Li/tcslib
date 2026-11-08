<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleTM.runWith_take_eq_of_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Runs Under Agreeing Queries

**Claim.** If the two oracles give the same answer to every query encountered in the run using $O$ before the first $|w|$ choices, then the configurations using the first $s$ choices agree for every $s\le |w|$.

**Proof.** Use induction on $s$. At $s=0$, both runs start in the same initial configuration. For the successor case, the bound $s+1\le |w|$ ensures that the next choice bit $w[s]$ exists and that the hypothesis applies at the configuration reached after the first $s$ bits. The induction hypothesis identifies that configuration for the two oracles. With the choice bit fixed, each nondeterministic step is the deterministic step of the corresponding fixed-choice machine (`Turing.OracleNDTM.stepWith_eq_fixChoice_step`). The step-equality result (`Turing.OracleTM.step_eq_of_query_agree`) says these steps agree when the current query receives the same membership answer from both oracles; its hypothesis holds if the configuration is in the query state, and otherwise the step does not depend on the oracle. Thus the configurations after the next choice agree. The run-append identity (`Turing.OracleNDTM.runWith_append`) expresses each run through $s+1$ bits as first running the initial $s$ bits and then taking this one step, completing the induction.

**Key facts.** `Turing.OracleNDTM.runWith_append`, `Turing.OracleNDTM.stepWith_eq_fixChoice_step`, `Turing.OracleTM.step_eq_of_query_agree`.
