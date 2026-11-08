<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.windowRun_tag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accumulator Tracks the Output Word

**Claim.** If $\sigma$ updates compatibly with appending each optional Boolean, then a windowed run initialized with $\sigma$ of the initial output returns $\sigma$ of the output in its returned configuration.

**Proof.** Induct on the clock bound. With zero clock, the run returns the initial configuration and accumulator unchanged, so the claim follows immediately. For a positive clock, if the initial configuration is halted, the run again returns it unchanged. If it is nonhalting but its successor is outside the window, it reports leaving and also returns the initial data unchanged. In the remaining case it proceeds to the successor and updates the accumulator by applying $\mathrm{upd}$ to the current accumulator and the emitted optional Boolean. By `step_output`, the successor's output is the current output with that optional Boolean appended. The compatibility hypothesis for $\sigma$ therefore identifies the updated accumulator with $\sigma$ of the successor's output. The induction hypothesis applied to the smaller-clock run from that successor now gives the desired equality.

**Key facts.** `Turing.MultiTapeTM.step_output`.
