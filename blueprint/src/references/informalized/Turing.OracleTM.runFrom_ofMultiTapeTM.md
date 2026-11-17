<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_ofMultiTapeTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lockstep Simulation of a Plain Machine

**Claim.** At every time $t$, the oracle machine associated to a plain machine simulates its run step for step, with the configuration embedded into the larger state and tape space.

**Proof.** Proceed by induction on $t$. At time zero, both sides are the same embedded starting configuration. For the successor step, express the oracle run at time $t+1$ as one oracle transition applied to its time-$t$ configuration. The induction hypothesis identifies that configuration with the embedding of the plain run. The one-step simulation theorem (`Turing.OracleTM.step_ofMultiTapeTM`) says that the oracle transition on an embedded configuration is exactly the embedding of the plain machine's next configuration. The plain-run successor equation (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) identifies that next configuration with the plain run at time $t+1$, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.OracleTM.step_ofMultiTapeTM`.
