<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.exists_windowRunnerTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-window simulation

**Claim.** There is a finite-state machine with an additional clock tape that simulates a window-limited run until it halts, leaves the window, or exhausts the encoded clock. It reaches the corresponding distinct exit state within the stated bound, preserves output, satisfies the head and space bounds, and records the resulting configuration and patched clock tape whenever the outcome is not exhaustion.

**Proof.** Start with the window-loop machine, whose ordinary run simulates the window-limited computation and whose stops represent halt, leaving the window, or exhaustion. Apply the clocked-simulation theorem to that machine, marking its halt and window-exit states as stopping states. The clock construction either reaches one of these genuine stops before the clock expires or reaches its timeout control; distinct tagged controls turn these outcomes into the required three exit states.

If a genuine stop is reached, choose its first occurrence. The loop's endpoint record identifies the corresponding window-run outcome, and uniqueness of any non-exhausted window outcome shows that this outcome agrees with every compatible horizon. The clock theorem supplies the time bound, the absence of earlier terminal states, the simulated configuration correspondence, and the patched clock word. If no genuine stop occurs before timeout, the clock theorem's timeout guarantee and the loop's cofinal exhausted endpoints rule out a spurious earlier halt or window-exit report. Thus the result is exhaustion. The loop's head-displacement and output invariants transfer through the clock simulation; the clock tape stays in its prescribed interval. The head bound implies the space estimate by counting the interval of possible visited positions on each tape.

**Key facts.** `Turing.exists_windowLoopTM`, `Turing.exists_stepClockTMVia`, `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`, `Turing.windowRun_stop_unique`.
