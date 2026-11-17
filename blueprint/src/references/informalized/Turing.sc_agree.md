<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Clock Transitions

**Claim.** For a state not marked to stop and a counter phase other than a completed phase, the clock machine’s transition agrees with the embedded Boolean decrement transition after relabeling its successor phase according to the saved body state.

**Proof.** Split on the counter phase. In the running phase, the assumption that the body state is not marked to stop makes the clock machine take its decrement branch; its transition is exactly the embedded decrement transition with the phase relabeled by the saved body state. In a rewind phase, the clock machine likewise uses the decrement branch, and the same relabeling gives the stated transition. A completed phase is excluded by hypothesis, so these cases exhaust the possibilities.
