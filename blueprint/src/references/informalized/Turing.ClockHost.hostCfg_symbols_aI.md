<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.hostCfg_symbols_aI -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Symbols on Attempt Tapes

**Claim.** For every attempt-tape index, the symbol read by its head in the host configuration is the content of that attempt tape at its chosen head position.

**Proof.** The host configuration places the yardstick tapes, attempt tapes, and extra tape in consecutive blocks of work-tape slots. The index assigned to an attempt tape lies in the middle block, where the slot function returns that tape's contents and its corresponding head position. Evaluating the read symbol at that slot therefore gives the attempt tape's contents at its head position.
