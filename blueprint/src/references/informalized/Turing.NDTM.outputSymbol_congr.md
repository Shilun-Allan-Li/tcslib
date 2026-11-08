<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.outputSymbol_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Depends Only on Core Configuration Data

**Claim.** For configurations whose states, input-head positions, work-tape contents, and work-head positions agree, the deterministic machine emits the same optional output symbol in one step.

**Proof.** Equality of the core data gives equality of the four components: state, input-head position, work-tape contents, and work-head positions. Thus the configurations themselves agree in all data used to determine the symbol read from the input and work tapes. If the common state is halted, both output symbols are none. If it is an ordinary state, both configurations supply the same state and read symbols to the same deterministic transition function, so the emitted optional symbol is identical.
