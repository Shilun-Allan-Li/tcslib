<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.parallelTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact configuration correspondence

**Claim.** After every number $t$ of steps, the transverse binary realization’s configuration on $x$ is exactly the transverse encoding of the original machine’s configuration on the symbolwise image of $x$.

**Proof.** Proceed by induction on $t$. At time zero, the encoded initial configuration is the binary machine’s initial configuration, by `Complexity.parallelCfg_init`. For the induction step, express each run at time $t+1$ as one step applied to the run at time $t` (the successor-time run identity, `Turing.MultiTapeTM.runFrom_succ_eq_step'`). Replace the binary run at time $t$ by the encoded original run using the induction hypothesis. The one-step correspondence `Complexity.parallelTM_step` says that stepping this encoded configuration gives exactly the encoding of the original machine’s next configuration. Rewriting the latter as its run at time $t+1$ proves the induction step.

**Key facts.** `Complexity.parallelCfg_init`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.parallelTM_step`.
