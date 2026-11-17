<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.freeLiteralPositions_fixCoordinateList_eq_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixing Free Literal Positions

**Claim.** After fixing, according to $x$, every coordinate that was free and occurs in $T$, no literal coordinate remains free.

**Proof.** Suppose, toward a contradiction, that some position $j$ is still free after the listed coordinates have been fixed. A coordinate that remains free after this procedure must have been free originally (\texttt{CoordRestriction.fixCoordinateList\_free\_imp\_original\_free}). Thus $j$ was among the original free literal positions. By the definition of the list of coordinates attached to those positions (\texttt{mem\_coordinatesAtPositions\_iff}), the coordinate of the literal at $j$ occurs in the list being fixed. But each coordinate in that list is no longer free after the fixing procedure (\texttt{CoordRestriction.fixCoordinateList\_ne\_free\_of\_mem}), contradicting the supposition. Hence there are no such positions, so the set of free literal positions is empty.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_free_imp_original_free`, `FABL.DNFTerm.mem_freeLiteralPositions_iff`, `FABL.DNFTerm.mem_coordinatesAtPositions_iff`, `FABL.CoordRestriction.fixCoordinateList_ne_free_of_mem`.
