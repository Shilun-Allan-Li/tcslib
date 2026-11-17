<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arReadCfg_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Read Sweep at Counter Zero

**Claim.** If the original configuration is in state $q$, its read-sweep configuration at counter zero is its encoded configuration.

**Proof.** At counter zero, the read buffer has no filled entries, by the empty-buffer identity (`Turing.FinTM.arBuffer_zero`). The state condition identifies the read-sweep state at counter zero with the ready encoding of the original state. The encoded configuration and the read-sweep configuration therefore have the same state, input position, work tapes, work-head positions, and output; hence they are equal.

**Key facts.** `Turing.FinTM.arBuffer_zero`.
