<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_plainEmptyOracle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-Oracle Simulation

**Claim.** Running the plain machine obtained by eliminating the oracle agrees at every time with running the original oracle machine using the empty language.

**Proof.** Induct on the number of steps. The claim at time zero follows because both runs start from the same configuration. For the successor, rewrite each run as one step from its time-$t$ configuration using the plain-run successor equation (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) and the iterate successor equation for the oracle run. The induction hypothesis makes those configurations equal, and the one-step empty-oracle simulation theorem (`Turing.OracleTM.step_plainEmptyOracle`) identifies the resulting transitions. Thus the runs agree at time $t+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.OracleTM.step_plainEmptyOracle`.
