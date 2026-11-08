<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.pcfg_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Buffer Configuration

**Claim.** With all three auxiliary words empty, the buffered configuration equals the configuration with blank auxiliary tapes, all three auxiliary heads at zero, and the same state, input-head position, and empty output.

**Proof.** Unfolding the buffered configuration shows that each auxiliary tape is represented by the buffer function applied to the empty word. At every integer position this function returns no symbol, so each such tape is the blank tape. The three head positions are the lengths of the empty words, hence zero, and the state, input-head position, and output agree by construction. Thus the configurations agree in every component.
