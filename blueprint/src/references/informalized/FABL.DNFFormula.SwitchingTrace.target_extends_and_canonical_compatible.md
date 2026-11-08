<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.SwitchingTrace.target_extends_and_canonical_compatible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Target Extension and Compatibility

**Claim.** Every switching trace’s target restriction extends the initial restriction, preserving its fixed coordinates, and some canonical term compatible with the initial restriction is also compatible with the target.

**Proof.** Induct on the trace. For a final trace, write $T$ for the canonical term and form the list of coordinates at the selected positions. Each such coordinate is free initially, since the positions lie among the free literal positions. Fixing these coordinates therefore gives a restriction extending the initial one (`FABL.CoordRestriction.extends_fixCoordinateList`). The term remains compatible after these fixes: it was compatible initially by the canonical-term compatibility fact (`FABL.DNFFormula.canonicalTerm_compatible'`), and the satisfying assignment has relative bit zero at every free literal position, so the position-fixing compatibility lemma applies (`FABL.DNFTerm.compatible_fix_positions`).

For a cons trace, let $T$ be the canonical term, and fix the coordinates of all its free literal positions. Denote the restriction obtained using the trace’s assignment by $\eta$, and the restriction obtained using $T$’s satisfying assignment by $\sigma$. Both lists use coordinates free in the initial restriction. Thus $\sigma$ extends the initial restriction. By the induction hypothesis, $\eta$ extends to the tail target; applying the parallel-fixing lemma transfers this extension to the restriction obtained by fixing the same block in the tail target using $T$’s satisfying assignment (`FABL.CoordRestriction.Extends.parallel_fixCoordinateList`). Transitivity of extension then shows that the original restriction extends to the trace target (`FABL.CoordRestriction.Extends.trans`).

The satisfying extension of $T$ is compatible with $T$ (`FABL.DNFTerm.satisfyingExtension_compatible`). After fixing the whole free block, $T$ has no free literal positions (`FABL.DNFTerm.freeLiteralPositions_fixCoordinateList_eq_empty`). Compatibility is preserved under any further extension once the term has no free literal positions (`FABL.DNFTerm.compatible_of_extends_of_no_free`), so $T$ is compatible with the trace target. The original canonical-term witness $hcompat$ serves in both cases.

**Key facts.** `FABL.DNFTerm.mem_coordinatesAtPositions_iff`, `FABL.DNFTerm.mem_freeLiteralPositions_iff`, `FABL.CoordRestriction.extends_fixCoordinateList`, `FABL.DNFFormula.canonicalTerm_compatible'`, `FABL.DNFTerm.relativeBit_satisfyingAssignment`, `FABL.DNFTerm.compatible_fix_positions`, `FABL.DNFFormula.SwitchingTrace.target_extends`, `FABL.CoordRestriction.Extends.parallel_fixCoordinateList`, `FABL.CoordRestriction.Extends.trans`, `FABL.DNFTerm.satisfyingExtension_compatible`, `FABL.DNFTerm.freeLiteralPositions_fixCoordinateList_eq_empty`, `FABL.DNFTerm.compatible_of_extends_of_no_free`.
