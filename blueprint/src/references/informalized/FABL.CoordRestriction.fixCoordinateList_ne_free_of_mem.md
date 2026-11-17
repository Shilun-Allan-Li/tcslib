<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.fixCoordinateList_ne_free_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Listed Coordinates Are Nonfree

**Claim.** Every coordinate in the list is nonfree after successively fixing the listed coordinates according to $x$.

**Proof.** Induct on the list, allowing the initial assignment to vary. There are no coordinates to check for the empty list. For a list with head $i$ and tail $L'$, decompose the update into the update at $i$ followed by the tail. If the coordinate under consideration lies in $L'$, the induction hypothesis applies directly to the tail. Otherwise it must be $i$. In that case, if $i$ also occurs in the tail, the induction hypothesis again gives the result. If it does not, the updates over the tail leave its value unchanged (`fixCoordinateList_apply_of_not_mem`), while the first update sets it to the fixed state for the encoded sign (`fixCoordinate_apply_self`). A fixed state is never free (`fixedState_ne_free`), proving the claim.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_cons`, `FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem`, `FABL.CoordRestriction.fixCoordinate_apply_self`, `FABL.CoordRestriction.fixedState_ne_free`.
