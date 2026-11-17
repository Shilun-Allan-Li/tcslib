<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.canonicalBlockTreeRaw_wellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formedness of the Raw Block Tree

**Claim.** For any restriction, the raw block tree is well formed relative to the full set of coordinates.

**Proof.** The raw tree is the auxiliary construction with fuel $n$. Apply the auxiliary well-formedness theorem at that fuel and the given restriction. Every coordinate free in the restriction belongs to the full coordinate set, so its free-within hypothesis holds (`FABL.CoordRestriction.freeWithin_univ`). The conclusion is exactly well-formedness of the raw tree relative to all coordinates (`FABL.DNFFormula.canonicalBlockTreeAux_wellFormed`).

**Key facts.** `FABL.CoordRestriction.freeWithin_univ`, `FABL.DNFFormula.canonicalBlockTreeAux_wellFormed`.
