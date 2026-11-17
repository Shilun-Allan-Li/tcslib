<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_clockDebit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clocked decrement segment

**Claim.** Starting from the clock configuration whose counter tape encodes $w$ and whose body state is $s$, the clocked machine completes the decrement phase in $2|w\mathbin{\mathrm{takeWhile}(\mathrm{not})}|+2$ steps. It reaches the state and patched tape specified by whether the decrement is defined, avoids finish and timeout states beforehand, and keeps the counter head within the stated interval while preserving the underlying configuration throughout.

**Proof.** Apply the clock-specific decrement transition agreement and the injectivity of the phase-to-clock-state map to the general decrement-run result (`sc_debit`). This gives the endpoint and, at every time through the endpoint, the frame description of the run and the counter-head bound. To show the run avoids the clock machine's exit states, take any earlier time. The phase-tracking conclusion of `sc_debit` says the current state is the image of a counter phase. The run and rewind phases map to decrement states, so cannot be finish or timeout states; a completed phase would contradict the earlier-time exclusion supplied by `sc_debit`. Finally, apply the observed-segment principle (`sc_observedSegment`) to this exit avoidance and the counter-head bounds. Its endpoint is the claimed configuration by the endpoint equation, yielding the required segment together with the frame description.

**Key facts.** `Turing.sc_debit`, `Turing.sc_decExit_injective`, `Turing.sc_observedSegment`.
