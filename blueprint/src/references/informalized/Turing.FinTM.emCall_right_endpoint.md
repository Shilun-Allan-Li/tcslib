<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_right_endpoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right-Boundary Scan Endpoint

**Claim.** If the source run from its initial configuration is halted at time $T$, then after exactly $T+|x|+2$ steps the right-boundary wrapper is in the scan configuration built from that halted run, with its administrative state halted and input head at position $|x|+1$.

**Proof.** Choose the earliest time $t$ at which the source run is halted. It exists because the run is halted at time $T$, and $t\le T$. The source configuration at time $t$ is halted, so all later source configurations equal it; the run composition law gives that the configuration at time $T$ is this same configuration (`Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`). Before time $t$, the source remains live, so the wrapper simulates it faithfully through time $t$ (`Turing.FinTM.emCall_right_run`). From the embedded halted configuration, the wrapper can finish its rightward scan in at most $|x|+2$ steps (`Turing.FinTM.emCall_right_finish`). Combining these two run segments gives a scan endpoint by time $T+|x|+2$. That endpoint is halted, so the wrapper remains there for any remaining steps; another application of run composition and halting stability identifies its configuration at exactly $T+|x|+2$ with the stated scan configuration.

**Key facts.** `Turing.FinTM.emCall_right_run`, `Turing.FinTM.emCall_right_finish`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
