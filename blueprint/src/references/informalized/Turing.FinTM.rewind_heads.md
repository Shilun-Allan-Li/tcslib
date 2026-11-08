<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.rewind_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Input Head

**Claim.** From any configuration in the start state, the machine reaches the destination state with its input head at position $1$ after at most $p+2$ steps, where $p$ is the initial input-head position; the other configuration components are unchanged, and work-tape head positions remain fixed throughout.

**Proof.** The first transition takes the machine from the start state to the scan state, moves the input head one position left, and leaves all other components unchanged. The input-head position after this step is $p-1$ (`moveInputPos_neg_val`). Since it is a valid position, it is at most the input length. The leftward-scan result (`rewind_scan`) now applies: from that configuration, after $(p-1)+1$ further steps the machine is in the destination state at position $1$, with its other components unchanged. Combining the initial step with these steps gives $1+((p-1)+1)$ steps, which is at most $p+2$. For work-head positions, time $u=0$ gives the original configuration directly. For $u>0$, separate the first step and apply the scan head-position result (`rewind_scan_heads`) to the remaining $u-1$ steps. It says the work-head positions stay fixed throughout that scan, and the initial transition also leaves them fixed.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.FinTM.rewind_scan`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.rewind_scan_heads`.
