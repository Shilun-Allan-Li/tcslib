<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitRetTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Return-State Simulation

**Claim.** Under the stated liveness and halting assumptions, the return-state simulation agrees with the embedded original run before time $T$, reaches the embedded terminal configuration with the distinguished right-summand state at time $T$, and does not enter that state earlier.

**Proof.** Apply the general through-halting simulation theorem `Turing.embedThroughHalt` to the return-state machine, using the embedded configuration as the configuration map. Its state is unchanged by this embedding. The one-step compatibility hypothesis is exactly `Turing.embedEmitRet_step`, which identifies a simulated step from an active configuration with the embedded next configuration, assigning the distinguished return state when the original step halts. The hypotheses that the initial state and every state before $T$ are live, and that the state at $T$ is halted, are precisely those required by the theorem. Its three conclusions give agreement before $T$, the stated terminal configuration at $T$, and exclusion of the return state before $T$.

**Key facts.** `Turing.embedEmitRet_step`, `Turing.embedThroughHalt`.
