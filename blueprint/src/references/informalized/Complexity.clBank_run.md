<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBank_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bank Runs Project to Counter Runs

**Claim.** After any number of steps, the bank run from the product configuration equals the product of the individual counter runs for the same number of steps.

**Proof.** Proceed by induction on the number of steps. At zero steps, both sides are the initial product configuration. For the successor case, the run after one additional step is obtained by taking one bank step after the run so far (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). Apply the induction hypothesis to identify the current bank configuration as the product of the counter configurations, then use the componentwise one-step identity (`Complexity.clBank_step`). The resulting configuration is exactly the product of the counter runs after one additional step.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.clBank_step`.
