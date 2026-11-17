<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.compatible_fix_positions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility after fixing selected literals

**Claim.** If a restriction is compatible with a conjunction of literals, a selected set of literal positions has free coordinates, and a binary assignment has relative bit $0$ at every free literal position, then fixing the selected coordinates to the signs encoded by that assignment preserves compatibility.

**Proof.** Take a witness $y$ for compatibility with the original restriction, and use $x$ as the witness for the restriction after the selected coordinates are fixed. The coordinates selected from distinct literal positions are distinct (`DNFTerm.coordinatesAtPositions_nodup`), and each is free: membership of a coordinate in the selected list identifies a selected position (`DNFTerm.mem_coordinatesAtPositions_iff`), which lies among the free literal positions by the subset hypothesis; the characterization of those positions then gives freeness (`DNFTerm.mem_freeLiteralPositions_iff`). Consequently, fixing the selected list does not change its completion with $x$ (`CoordRestriction.complete_fixCoordinateList`).

To verify that the resulting sign vector satisfies the conjunction, use the criterion that a conjunction evaluates to $-1$ exactly when every literal has its required sign (`DNFTerm.eval_eq_neg_one_iff`). At any free literal coordinate, relative bit $0$ makes $x$ equal to the binary encoding of that literal's required sign, so its completed sign is correct. At any nonfree literal coordinate, the restriction is unchanged by the fixing operation, and the original witness $y$ satisfied that literal. Thus all literals are satisfied by the new completion, establishing compatibility.

**Key facts.** `FABL.CoordRestriction.complete_fixCoordinateList`, `FABL.DNFTerm.coordinatesAtPositions_nodup`, `FABL.DNFTerm.mem_coordinatesAtPositions_iff`, `FABL.DNFTerm.mem_freeLiteralPositions_iff`, `FABL.DNFTerm.eval_eq_neg_one_iff`.
