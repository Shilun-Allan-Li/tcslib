<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.hostCfg_symbols_yI -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbol on the Extra Tape

**Claim.** The symbol read by the head on the extra tape in the host configuration is the content of that tape at its chosen head position.

**Proof.** The extra tape occupies the final work-tape slot. At its designated index, the host configuration's slot functions return the extra tape's contents and head position. Evaluating the read symbol gives the contents of that tape at that position.
