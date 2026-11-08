<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordinateDecisionTree.fixCoordinateList_assignCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction After Coordinate Assignment

**Claim.** Fixing the coordinates in $C$ according to $x$ gives the same restriction whether the values are read from $x$ or from the assignment obtained by updating $s$ on $C$ with those values.

**Proof.** The restriction produced by fixing a list depends only on the vector's values at coordinates in that list (`fixCoordinateList_congr`). By the queried-coordinate assignment property, the assignment obtained from $s$ agrees with $x$ at every coordinate in $C$ (`assignCoordinates_eq_on_mem`). Applying the congruence fact to these two vectors gives the asserted equality of restrictions.

**Key facts.** `FABL.CoordinateDecisionTree.fixCoordinateList_congr`, `FABL.CoordinateDecisionTree.assignCoordinates_eq_on_mem`.
