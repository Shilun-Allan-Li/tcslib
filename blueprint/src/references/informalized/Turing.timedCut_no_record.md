<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_no_record -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Pending Action Before a Live Endpoint

**Claim.** If $s<t$ and the interpreter has a present state at time $t$, then at time $s$ its control state is not any pending-action state.

**Proof.** Fix action bits and a halting flag, and suppose the control state at time $s$ is the corresponding pending-action state. Since $s<t$, we have $s+1\le t$. Backward persistence of liveness (`timedCut_live_before`) implies that the configuration at time $s+1$ has a present state. But one interpreter step from a pending-action state halts, so its state at time $s+1$ is absent. The successor-run identity (`runFrom_succ_eq_step'`) identifies this next configuration with the run at time $s+1$, giving a contradiction.

**Key facts.** `Turing.timedCut_live_before`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
