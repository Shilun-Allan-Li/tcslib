<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.restrict_extendCNFAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction after extension

**Claim.** Extending an assignment on the original variables by any auxiliary assignment and then restricting to the original variables recovers the original assignment.

**Proof.** To prove equality of assignments, compare their values at an arbitrary original coordinate. The restriction reads the extended assignment at that same coordinate, and the extension assigns it the original value there. Thus the two assignments agree at every coordinate.
