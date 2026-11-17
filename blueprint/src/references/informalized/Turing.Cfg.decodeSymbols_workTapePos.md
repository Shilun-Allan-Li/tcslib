<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.decodeSymbols_workTapePos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Head Preservation

**Claim.** Decoding a configuration leaves all work-tape head positions unchanged.

**Proof.** The decoded configuration is defined with work-tape head positions exactly those of $D$. Hence the position functions are equal.
