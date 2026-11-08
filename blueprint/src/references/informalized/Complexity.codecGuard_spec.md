<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecGuard_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration decoded by a guard

**Claim.** For a configuration in the stated work-window, the wired guard holds exactly when its state, input-head position, work-head positions, and scanned symbols agree with the data specified by the position tuple and case.

**Proof.** First use the guard's row characterization (`Complexity.codecGuard_rows`) with the encoding of the configuration as the first row. The resulting conditions assert equality of its encoded state and input-head position with the case and selected position, equality of every encoded work-head position with its selected position, and agreement of the encoded scanned symbols with the case. For each work tape, the position-code equivalence (`Complexity.codec_posCode_eq_iff`), applicable because the head lies within radius $s$, converts equality of the encoded head position to the assertion that the actual head is at the integer position $p_i-s$. The input-read wire identity (`Complexity.codecInputRead_wire`) converts the encoded input-read condition to equality with the configuration's scanned input symbol. Finally, by the definition of the row encoding, its work-tape symbol at the selected encoded position is the tape content at integer position $p_i-s$; using the head-position equality identifies this with the scanned work-tape symbol. Reversing these same equivalences proves the converse.

**Key facts.** `Complexity.codecGuard_rows`, `Complexity.codec_posCode_eq_iff`, `Complexity.codecInputRead_wire`.
