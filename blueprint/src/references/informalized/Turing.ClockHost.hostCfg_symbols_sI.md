<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.hostCfg_symbols_sI -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Symbols on Yardstick Tapes

**Claim.** For every yardstick-tape index, the symbol read by its head in the host configuration is the content of that yardstick tape at its chosen head position.

**Proof.** The host configuration places the yardstick tapes in the first block of work-tape slots. The index assigned to a yardstick tape selects that block's corresponding tape contents and head position. Thus the symbol read there is the yardstick tape's contents at its chosen head position.
