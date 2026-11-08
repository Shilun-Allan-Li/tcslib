<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_track_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact tracked simulation

**Claim.** For every time $t$, running the tracked machine for $1+2t$ steps yields exactly the completed tracked configuration of the original machine after $t$ steps, with each tape's span recording the leftmost and rightmost head positions visited through time $t$.

**Proof.** Use induction on $t$. At $t=0$, the assertion is the tracked initialization identity (`emCall_track_initial`). For the successor step, write $c$ for the original configuration at time $t$. The run-length identity for iterated steps splits the next run into the first $1+2t$ steps, followed by two steps (`runFrom_add`); the induction hypothesis identifies the configuration at that split. Also, one original step takes $c$ to the configuration at time $t+1$ (`runFrom_succ_eq_step'`).

If $c$ is halted, its next configuration is unchanged (`step_of_halt`), so the leftmost and rightmost bounds do not change: the current head already lies within them by the visited-interval bounds (`emCall_track_extent`). The tracked configuration is halted as well, and its next two steps leave it fixed (`runFrom_of_halt` and `step_of_halt`).

If $c$ is active, its head moves by at most one cell (`workTapePos_step_le`). Hence the next head position lies within one cell of the old bounds. The tracked machine first simulates the original transition while entering its intermediate stamping state (`emCall_track_action`), then stamps the new head position into the marker banks and updates the span to the minimum and maximum of the old bounds and the new position (`emCall_track_stamp`). The definitions of the span bounds use exactly those minimum and maximum updates, so this is the completed tracked configuration at time $t+1$.

**Key facts.** `Turing.FinTM.emCall_track_initial`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_of_halt`, `Turing.FinTM.emCall_track_extent`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.workTapePos_step_le`, `Turing.FinTM.emCall_track_action`, `Turing.FinTM.emCall_track_stamp`.
