<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.mem_coordinatesAtPositions_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinates Selected by Positions

**Claim.** A coordinate occurs in the list of coordinates selected by a set of literal positions exactly when some selected position contains a literal with that coordinate.

**Proof.** The list of selected coordinates is obtained by mapping the chosen positions, in their list order, to the indices of their literals. Membership in a mapped list means that some element of the source list maps to the given coordinate. Membership in the list of positions is exactly membership in the specified set of positions, yielding the stated existential characterization.
