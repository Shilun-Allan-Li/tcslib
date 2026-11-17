<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.prepInvariant_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation invariant along the run

**Claim.** At every time $t$, the logical simulator's configuration on the embedded input is the decorated schedule configuration for some data register, data tapes, and output list, and those components satisfy the preparation invariant.

**Proof.** Proceed by induction on $t$. At time zero, take the initial data register, blank data tapes, and empty output. The decorated initial-configuration identity (`decoratedCfg_init`) identifies the simulator's start configuration with the schedule's start configuration carrying those components; the initial phase conditions give the invariant. For the successor step, use the induction hypothesis and write $c$ for the schedule configuration at time $t$. If $c$ is halted, both machines remain at their respective configurations, by the halting-step property (`Turing.MultiTapeTM.step_of_halt`), so the same components work. If $c$ is in a live state, let the data transducer's visit produce its updated register, tape-write instructions, and optional output. The decorated-step identity (`decoratedCfg_step`) identifies the simulator's next configuration with the decoration of the schedule's next configuration using precisely those updates. The one-step preservation theorem (`Complexity.prepInvariant_step`) says that these same updates preserve the preparation invariant. In both cases, the induction hypothesis therefore supplies the required components at time $t+1$.

**Key facts.** `Complexity.decoratedCfg_init`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_of_halt`, `Complexity.decoratedCfg_step`, `Complexity.prepInvariant_step`.
