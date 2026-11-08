<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.DNFFormula.firstCompatibleTerm_compatible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility of the First Term

**Claim.** The term at the first compatible term index is compatible with the restriction.

**Proof.** The first compatible index belongs to the filtered set of compatible term indices (by `firstCompatibleTermIndex_mem`). Membership in this filtered set means precisely that the term retrieved at that index is compatible with the restriction.

**Key facts.** `FABL.DNFFormula.firstCompatibleTermIndex_mem`.
