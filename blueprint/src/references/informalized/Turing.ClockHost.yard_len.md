<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.yard_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Yardstick endpoint is blank

**Claim.** For every natural number $m$, the yardstick tape of length $m$ is blank at cell $m$.

**Proof.** At the natural-number position $m$, the yardstick agrees with the length-$m$ list of $m$ true symbols, viewed as a tape. A list lookup at index $m$ is out of range for a list of length $m$, so this lookup is absent and the tape is blank there.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
