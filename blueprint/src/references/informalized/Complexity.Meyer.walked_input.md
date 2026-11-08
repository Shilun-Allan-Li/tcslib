<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.walked_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol After Repeated Walks

**Claim.** After $a$ repetitions of the simulated input-head walk, the scanned symbol is the symbol of $x$ at the original input-head position shifted by $-a$ when $neg$ is true and by $a$ otherwise, with out-of-range positions interpreted as blank.

**Proof.** The iterate formula for an input-only simulated walk (`wstep_none_iterate`) reduces the claim to tracking repeated moves of the input head. The input-symbol identification theorem (`inputSymbol_eq_xhat`) expresses the scanned symbol as the word lookup at the shifted head position. If the direction is positive, repeated movement places the head at the smaller of its original position plus $a$ and the right boundary (`iterate_move_pos`). If this position is within the input range, the lookup is the corresponding entry of $x$; if it has reached the boundary, both lookups are absent, so the scanned symbol is blank. If the direction is negative, repeated movement places the head at the original position minus $a$ (`iterate_move_neg`); when $a$ exceeds that position, the head has saturated at the left boundary and both lookups are blank. In the remaining case the shifted position is exactly the original position minus $a$, as required. The flag $bl$ does not affect the simulated movement.

**Key facts.** `Complexity.Meyer.wstep_none_iterate`, `Complexity.Meyer.inputSymbol_eq_xhat`, `Complexity.Meyer.iterate_move_pos`, `Complexity.Meyer.iterate_move_neg`.
