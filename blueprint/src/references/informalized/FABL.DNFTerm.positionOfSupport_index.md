<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.positionOfSupport_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate of the Selected Literal

**Claim.** For any coordinate in the support of a term, the literal selected at that coordinate has that coordinate as its index.

**Proof.** The selected position retrieves the literal chosen for $i$ (`get_positionOfSupport`). That chosen literal has index $i$ (`literalAt_index`), so the literal at the selected position does as well.

**Key facts.** `FABL.DNFTerm.get_positionOfSupport`, `FABL.DNFTerm.literalAt_index`.
