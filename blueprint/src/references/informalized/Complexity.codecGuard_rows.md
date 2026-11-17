<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecGuard_rows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guard condition in row form

**Claim.** The wired port assignment satisfies the codec guard exactly when the first row has the state, input-head position, work-head positions, and scanned symbols specified by the case and position data.

**Proof.** Unfolding the guard, the wiring, the pair-of-rows assignment, and the row encoding identifies the state and input-head port conditions with equality of the corresponding fields of the first row. Likewise, each work-head port condition says its encoded head equals the selected position. For each work tape, the two symbol flags decode to the recorded optional symbol: the flag identity `Complexity.codecReadSymbol_flags` says that the pair of flags for an optional Boolean symbol reads back that symbol. The input port condition is already the encoded input-read expression in the claimed row characterization. These reductions give both directions of the equivalence.

**Key facts.** `Complexity.codecReadSymbol_flags`.
