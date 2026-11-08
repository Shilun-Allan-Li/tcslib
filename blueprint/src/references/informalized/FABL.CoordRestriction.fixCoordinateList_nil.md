<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.fixCoordinateList_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty List Leaves Assignment Unchanged

**Claim.** Applying the coordinate-fixing procedure to the empty list leaves $\rho$ unchanged.

**Proof.** The procedure is a fold over the list of coordinates. Folding over the empty list performs no updates, so the result is $\rho$ by definition.
