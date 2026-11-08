<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.coordinatesAtPositions_nonempty_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty selected coordinates

**Claim.** The list of coordinates selected from a set of literal positions is nonempty exactly when that set of positions is nonempty.

**Proof.** The selected-coordinate list is formed by mapping the position list to coordinates. A mapped list is empty exactly when its source list is empty. The position list of a finset is empty exactly when the finset is empty, which is equivalent to its not being nonempty. Combining these equivalences gives the claim.
