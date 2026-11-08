<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.compatible_fix_freeLiteralPositions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility after fixing free literals

**Claim.** If a restriction is compatible with a conjunction of literals, and a binary assignment has relative bit $0$ at every literal position whose coordinate is free, then fixing all those free literal coordinates to the signs encoded by that assignment preserves compatibility.

**Proof.** Choose an assignment $y$ witnessing compatibility of the original restriction. We will use $x$ as the witness after fixing the specified coordinates. The completion lemma for fixing a list of distinct, originally free coordinates says that completing the new restriction with $x$ gives the same sign vector as completing the original restriction with $x$ (`CoordRestriction.complete_fixCoordinateList`). The selected coordinates are indeed distinct and free, by `DNFTerm.coordinatesAtPositions_nodup` and `DNFTerm.coordinatesAt_freeLiteralPositions_all_free`.

It remains to check every literal. A conjunction evaluates to $-1$ exactly when every literal receives its required sign (`DNFTerm.eval_eq_neg_one_iff`). For a literal at a free coordinate, its position belongs to the free literal positions; relative bit $0$ means the bit of $x$ equals the binary encoding of the required sign. Thus the sign encoded by $x$ at that coordinate is precisely the required sign. For a literal at a fixed coordinate, the original satisfying witness $y$ already gives its required sign, and the new completion agrees there because that coordinate was not changed. Hence every literal is satisfied, proving compatibility.

**Key facts.** `FABL.CoordRestriction.complete_fixCoordinateList`, `FABL.DNFTerm.coordinatesAtPositions_nodup`, `FABL.DNFTerm.coordinatesAt_freeLiteralPositions_all_free`, `FABL.DNFTerm.eval_eq_neg_one_iff`, `FABL.DNFTerm.mem_freeLiteralPositions_iff`.
