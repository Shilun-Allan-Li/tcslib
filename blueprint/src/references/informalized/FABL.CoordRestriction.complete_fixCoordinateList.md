<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.complete_fixCoordinateList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion after list fixing

**Claim.** Fixing a list of distinct coordinates that are all free in the original restriction, according to the signs encoded by $x$, leaves the completion using $x$ unchanged.

**Proof.** Proceed by induction on the list, allowing the starting restriction to vary. The empty list makes no changes. For a list with first coordinate $i$ and remaining tail $L$, expand the fold: first fix $i$ to the sign encoded by $x_i$, then process $L$. The induction hypothesis applies to this new starting restriction. Indeed, the tail has no repetitions, and each $j$ in it differs from $i$; fixing $i$ therefore leaves the restriction at $j$ unchanged (`fixCoordinate_apply_of_ne`), so every coordinate in the tail is still free. After the tail has been processed, the one-coordinate fact that fixing a free coordinate to the sign encoded by its current bit leaves completion unchanged (`complete_fixCoordinate_signEncode`) identifies the result with the completion under the original restriction.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_cons`, `FABL.CoordRestriction.fixCoordinate_apply_of_ne`, `FABL.CoordRestriction.complete_fixCoordinate_signEncode`.
