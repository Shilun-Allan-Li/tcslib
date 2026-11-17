<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.workTapeSymbols_eq_RW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Current Work Tape Read

**Claim.** For any configuration $c$ and work-tape index $h$, the symbol read on tape $h$ is the symbol stored at its head position, equivalently the symbol at offset zero from that head.

**Proof.** The read symbol is defined by evaluating tape $h$ at its head position. The offset-zero reading evaluates the same tape at head position plus zero, which is the same position. Thus the two values agree by the definitions of `Cfg.workTapeSymbols` and `RW`.
