<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.lenStart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Checker Startup After Simulation

**Claim.** If $M$ computes $w$ from $x$ within $T$ steps, then some configuration $c$ of $M$ on $x$ has output $w$, and the captured-length checker reaches the parse configuration at position $0$ with counter $|w|$ within $T+|x|+4$ steps, retaining $c$ as its simulated configuration.

**Proof.** The computation hypothesis supplies a halting time $T$ with output $w$ (`computesInTime_iff`). Choose the earliest halting time $t$; then $t\le T$, and the original machine has not halted at any earlier time. Let $c$ be its configuration at time $t$. It is halted, and its output is $w$, since outputs of computations by the same machine on the same input are unique (`ComputesInTime.output_unique`). The captured machine simulates the original machine for these $t$ steps: its initial configuration is the captured initial configuration, and `capture_run` applies because the original computation stays live before time $t$. At time $t$, the captured simulation is in its return state. One additional transition moves it into a ready checker configuration, preserving the simulated configuration. The rewind procedure then scans back to the input start and enters the parser state with the counter set to $|c.output|$ (`catalogRewind`). Its rewind length is bounded by the current input-head position plus two; together with $t+1$ this is at most $T+|x|+4$. Finally, composing these consecutive runs using `runFrom_add`, and expressing the first transition with `runFrom_succ_eq_step` and `runFrom_zero`, identifies the final configuration as the required `lenCfg`.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Turing.capture_run`, `Turing.FinTM.catalogRewind`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
