<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.yard_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Cell to the Left

**Claim.** For every natural number $m$, the yardstick tape of length $m$ is blank at cell $-1$.

**Proof.** The yardstick tape is a particular buffer tape, obtained by buffering a list of $m$ copies of $1$. The buffer tape is blank at cell $-1$ for every list (the fact `Turing.FinTM.bufferTape_left`), so the yardstick tape is blank there as well.

**Key facts.** `Turing.FinTM.bufferTape_left`.
