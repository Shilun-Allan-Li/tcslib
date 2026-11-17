<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_reset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Resetting the Input Head

**Claim.** Starting in reset-start phase, after $\max(p,1)+1$ steps the machine is in copy-left phase with input head at position $1$; controller tapes and their head positions, and all other configuration data, are unchanged.

**Proof.** The first reset-start transition enters reset-scan and moves the input head one position left, from $p$ to $p-1$ (with the finite input head bounded as in the statement). The proof then splits the run into this first step, the reset scan, and the final transition. The reset-scan result (`Complexity.setupCfg_reset_scan`) shows that after $p-1$ further steps the input head is at the left boundary, with the rest of the configuration unchanged. The final reset-scan transition sees the boundary symbol and enters copy-left, moving the input head right to position $1$ without altering the controller tapes or heads. The run decomposition identities `runFrom_add`, `runFrom_succ_eq_step`, and `runFrom_zero` justify combining these stages; the total number of steps is $(p-1)+2=\max(p,1)+1$ under the encoded input-head position.

**Key facts.** `Complexity.setupCfg_apply`, `Complexity.setupCfg_reset_scan`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
