<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.coordinatesAt_freeLiteralPositions_all_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinates at free literal positions

**Claim.** Every coordinate in the list selected from free literal positions is free under the restriction.

**Proof.** Take a coordinate in the selected list. By the membership characterization for coordinates selected at positions, it is the coordinate of some literal position belonging to the free literal positions (`DNFTerm.mem_coordinatesAtPositions_iff`). The characterization of membership in the free literal positions then says that the restriction at this coordinate is free (`DNFTerm.mem_freeLiteralPositions_iff`).

**Key facts.** `FABL.DNFTerm.mem_coordinatesAtPositions_iff`, `FABL.DNFTerm.mem_freeLiteralPositions_iff`.
